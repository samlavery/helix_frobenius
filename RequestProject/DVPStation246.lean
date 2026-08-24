import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 246` (rung-262.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT246 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((246 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((495907/500000 : ℚ) : ℝ))

theorem st246_c1 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((136793/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -495907/2000000) (δ := 1/1000000000) (ψ := 495907/500000) 246 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t1 : ((273561/500000 : ℚ) : ℝ) ≤ stT246 1 := by
  have hc : ((273561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((273561/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((273561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c2 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((992369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -154523/5000000) (δ := 3077/250000000) (ψ := 495907/500000) 246 27
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t2 : ((7016754134373/10000000000000 : ℚ) : ℝ) ≤ stT246 2 := by
  have hc : ((992319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7016754134373/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((992319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c3 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((153403/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1137711/5000000) (δ := 12393/1000000000) (ψ := 495907/500000) 246 43
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t3 : ((885600358531/2500000000000 : ℚ) : ℝ) ≤ stT246 3 := by
  have hc : ((306781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((885600358531/2500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((306781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c4 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((367683/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 930737/5000000) (δ := 12389/1000000000) (ψ := 495907/500000) 246 54
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t4 : ((183829/500000 : ℚ) : ℝ) ≤ stT246 4 := by
  have hc : ((183829/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183829/500000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((183829/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c5 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((613151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1138441/5000000) (δ := 12449/1000000000) (ψ := 495907/500000) 246 63
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t5 : ((548374088127/2000000000000 : ℚ) : ℝ) ≤ stT246 5 := by
  have hc : ((613101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((548374088127/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((613101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c6 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((12489/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -52451/5000000) (δ := 769/62500000) (ψ := 495907/500000) 246 70
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t6 : ((203934264587/500000000000 : ℚ) : ℝ) ≤ stT246 6 := by
  have hc : ((99907/100000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203934264587/500000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((99907/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c7 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((245961/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 449999/10000000) (δ := 12347/1000000000) (ψ := 495907/500000) 246 76
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t7 : ((464798886167/1250000000000 : ℚ) : ℝ) ≤ stT246 7 := by
  have hc : ((491897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((464798886167/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((491897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c8 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-41989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2015997/5000000) (δ := 12483/1000000000) (ψ := 495907/500000) 246 81
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t8 : ((-74315156913/5000000000000 : ℚ) : ℝ) ≤ stT246 8 := by
  have hc : ((-42039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74315156913/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-42039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c9 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((337987/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1035639/5000000) (δ := 387/31250000) (ψ := 495907/500000) 246 86
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t9 : ((563269943673/2500000000000 : ℚ) : ℝ) ≤ stT246 9 := by
  have hc : ((168981/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((563269943673/2500000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((168981/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c10 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((499547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -106423/10000000) (δ := 389/31250000) (ψ := 495907/500000) 246 90
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t10 : ((789813465797/2500000000000 : ℚ) : ℝ) ≤ stT246 10 := by
  have hc : ((249761/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((789813465797/2500000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((249761/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c11 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-78773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4322503/10000000) (δ := 3119/250000000) (ψ := 495907/500000) 246 94
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t11 : ((-59396238243/1250000000000 : ℚ) : ℝ) ≤ stT246 11 := by
  have hc : ((-39399/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59396238243/1250000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-39399/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c12 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((16941/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1032809/5000000) (δ := 6199/500000000) (ψ := 495907/500000) 246 97
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t12 : ((195603361009/1000000000000 : ℚ) : ℝ) ≤ stT246 12 := by
  have hc : ((67759/100000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((195603361009/1000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((67759/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c13 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-77/800 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1041997/2500000) (δ := 3121/250000000) (ψ := 495907/500000) 246 100
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t13 : ((-2670881463/100000000000 : ℚ) : ℝ) ≤ stT246 13 := by
  have hc : ((-963/10000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2670881463/100000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-963/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c14 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((3993/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2620519/10000000) (δ := 12441/1000000000) (ψ := 495907/500000) 246 103
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t14 : ((13338338339/100000000000 : ℚ) : ℝ) ≤ stT246 14 := by
  have hc : ((19963/40000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13338338339/100000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((19963/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c15 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((675543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1036369/5000000) (δ := 311/25000000) (ψ := 495907/500000) 246 106
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t15 : ((436028705021/2500000000000 : ℚ) : ℝ) ≤ stT246 15 := by
  have hc : ((675493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((436028705021/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((675493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c16 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-12338/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6202513/10000000) (δ := 6213/500000000) (ψ := 495907/500000) 246 108
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t16 : ((-987102894841/5000000000000 : ℚ) : ℝ) ≤ stT246 16 := by
  have hc : ((-394841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-987102894841/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-394841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c17 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((57819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3637247/10000000) (δ := 6249/500000000) (ψ := 495907/500000) 246 111
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t17 : ((17521378083/625000000000 : ℚ) : ℝ) ≤ stT246 17 := by
  have hc : ((28897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17521378083/625000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((28897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c18 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((249803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49621/5000000) (δ := 12313/1000000000) (ψ := 495907/500000) 246 113
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t18 : ((588761703891/2500000000000 : ℚ) : ℝ) ≤ stT246 18 := by
  have hc : ((499581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((588761703891/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((499581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c19 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((35761/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1934643/10000000) (δ := 3119/250000000) (ψ := 495907/500000) 246 115
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t19 : ((164071226169/1000000000000 : ℚ) : ℝ) ≤ stT246 19 := by
  have hc : ((71517/100000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164071226169/1000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((71517/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c20 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((84761/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 64503/312500) (δ := 12461/1000000000) (ψ := 495907/500000) 246 117
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t20 : ((758069198273/5000000000000 : ℚ) : ℝ) ≤ stT246 20 := by
  have hc : ((339019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((758069198273/5000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((339019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c21 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((965963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 654143/10000000) (δ := 3089/250000000) (ψ := 495907/500000) 246 119
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t21 : ((1053897049257/5000000000000 : ℚ) : ℝ) ≤ stT246 21 := by
  have hc : ((965913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1053897049257/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((965913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c22 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((162959/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -134499/625000) (δ := 12433/1000000000) (ψ := 495907/500000) 246 121
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t22 : ((694806157251/5000000000000 : ℚ) : ℝ) ≤ stT246 22 := by
  have hc : ((325893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((694806157251/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((325893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c23 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-796343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6230053/10000000) (δ := 2477/200000000) (ψ := 495907/500000) 246 123
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t23 : ((-332118976397/2000000000000 : ℚ) : ℝ) ≤ stT246 23 := by
  have hc : ((-796393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-332118976397/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-796393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c24 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-7709/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2118069/5000000) (δ := 3123/250000000) (ψ := 495907/500000) 246 124
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t24 : ((-62969253837/2500000000000 : ℚ) : ℝ) ≤ stT246 24 := by
  have hc : ((-61697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62969253837/2500000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-61697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c25 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((337547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2074259/10000000) (δ := 6153/500000000) (ψ := 495907/500000) 246 126
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t25 : ((168761/1250000 : ℚ) : ℝ) ≤ stT246 25 := by
  have hc : ((168761/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168761/1250000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((168761/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c26 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-32873/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1584627/2500000) (δ := 1239/100000000) (ψ := 495907/500000) 246 127
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t26 : ((-257892803/1600000000 : ℚ) : ℝ) ≤ stT246 26 := by
  have hc : ((-263/320 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-257892803/1600000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-263/320 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c27 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((73383/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -933567/5000000) (δ := 99/8000000) (ψ := 495907/500000) 246 129
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t27 : ((141215961/1000000000 : ℚ) : ℝ) ≤ stT246 27 := by
  have hc : ((36689/50000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141215961/1000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((36689/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c28 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-338779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2395519/5000000) (δ := 3117/250000000) (ψ := 495907/500000) 246 130
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t28 : ((-640326837267/10000000000000 : ℚ) : ℝ) ≤ stT246 28 := by
  have hc : ((-338829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-640326837267/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-338829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c29 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-431991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5043739/10000000) (δ := 6227/500000000) (ψ := 495907/500000) 246 132
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t29 : ((-401140131557/5000000000000 : ℚ) : ℝ) ≤ stT246 29 := by
  have hc : ((-432041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-401140131557/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-432041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c30 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((249809/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97721/10000000) (δ := 1557/125000000) (ψ := 495907/500000) 246 133
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t30 : ((912127423413/5000000000000 : ℚ) : ℝ) ≤ stT246 30 := by
  have hc : ((499593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((912127423413/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((499593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c31 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-124391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2277773/5000000) (δ := 3091/250000000) (ψ := 495907/500000) 246 134
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t31 : ((-218220561/4882812500 : ℚ) : ℝ) ≤ stT246 31 := by
  have hc : ((-3888/15625 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218220561/4882812500 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-3888/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c32 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-244631/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -733493/1000000) (δ := 6189/500000000) (ψ := 495907/500000) 246 136
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t32 : ((-864945412129/5000000000000 : ℚ) : ℝ) ≤ stT246 32 := by
  have hc : ((-489287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-864945412129/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-489287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c33 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-76473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4118359/10000000) (δ := 2497/200000000) (ψ := 495907/500000) 246 137
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t33 : ((-133209478371/10000000000000 : ℚ) : ℝ) ≤ stT246 33 := by
  have hc : ((-76523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133209478371/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-76523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c34 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((832777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -183341/1250000) (δ := 12411/1000000000) (ψ := 495907/500000) 246 138
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t34 : ((285622862819/2000000000000 : ℚ) : ℝ) ≤ stT246 34 := by
  have hc : ((832727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((285622862819/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((832727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c35 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((24153/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 326311/5000000) (δ := 12499/1000000000) (ψ := 495907/500000) 246 139
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t35 : ((40823896239/250000000000 : ℚ) : ℝ) ≤ stT246 35 := by
  have hc : ((96607/100000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40823896239/250000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((96607/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c36 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((615399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1134881/5000000) (δ := 12407/1000000000) (ψ := 495907/500000) 246 140
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t36 : ((512790628217/5000000000000 : ℚ) : ℝ) ≤ stT246 36 := by
  have hc : ((615349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((512790628217/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((615349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c37 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((204471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3412183/10000000) (δ := 12489/1000000000) (ψ := 495907/500000) 246 141
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t37 : ((336065875369/10000000000000 : ℚ) : ℝ) ≤ stT246 37 := by
  have hc : ((204421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((336065875369/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((204421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c38 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-71209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4105163/10000000) (δ := 6191/500000000) (ψ := 495907/500000) 246 142
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t38 : ((-23119483737/2000000000000 : ℚ) : ℝ) ≤ stT246 38 := by
  have hc : ((-71259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23119483737/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-71259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c39 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-177117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1093033/2500000) (δ := 499/40000000) (ψ := 495907/500000) 246 143
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t39 : ((-141847164047/5000000000000 : ℚ) : ℝ) ≤ stT246 39 := by
  have hc : ((-177167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141847164047/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-177167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c40 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-6137/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 529327/1250000) (δ := 773/62500000) (ψ := 495907/500000) 246 144
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t40 : ((-19414805781/1000000000000 : ℚ) : ℝ) ≤ stT246 40 := by
  have hc : ((-12279/100000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19414805781/1000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-12279/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c41 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((1713/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1856301/5000000) (δ := 12343/1000000000) (ψ := 495907/500000) 246 145
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t41 : ((167105859/12500000000 : ℚ) : ℝ) ≤ stT246 41 := by
  have hc : ((107/1250 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167105859/12500000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((107/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c42 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((213391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2824663/10000000) (δ := 249/20000000) (ψ := 495907/500000) 246 146
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t42 : ((164615389539/2500000000000 : ℚ) : ℝ) ≤ stT246 42 := by
  have hc : ((106683/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164615389539/2500000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((106683/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c43 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((804963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1587957/10000000) (δ := 12357/1000000000) (ψ := 495907/500000) 246 147
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t43 : ((245496050261/2000000000000 : ℚ) : ℝ) ≤ stT246 43 := by
  have hc : ((804913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245496050261/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((804913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c44 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((999973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2317/1250000) (δ := 12339/1000000000) (ψ := 495907/500000) 246 148
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t44 : ((376859979547/2500000000000 : ℚ) : ℝ) ≤ stT246 44 := by
  have hc : ((999923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((376859979547/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((999923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c45 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((733417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -373731/2000000) (δ := 12371/1000000000) (ψ := 495907/500000) 246 149
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t45 : ((1093238253937/10000000000000 : ℚ) : ℝ) ≤ stT246 45 := by
  have hc : ((733367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1093238253937/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((733367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c46 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-53017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -811919/2000000) (δ := 493/40000000) (ψ := 495907/500000) 246 150
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t46 : ((-3912152307/500000000000 : ℚ) : ℝ) ≤ stT246 46 := by
  have hc : ((-53067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3912152307/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-53067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c47 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-54079/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51103/78125) (δ := 12417/1000000000) (ψ := 495907/500000) 246 151
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t47 : ((-12621902661/100000000000 : ℚ) : ℝ) ≤ stT246 47 := by
  have hc : ((-432657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12621902661/100000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-432657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c48 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-837049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6406657/10000000) (δ := 12417/1000000000) (ψ := 495907/500000) 246 151
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t48 : ((-75515537889/625000000000 : ℚ) : ℝ) ≤ stT246 48 := by
  have hc : ((-837099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75515537889/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-837099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c49 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((217249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1689751/5000000) (δ := 1231/100000000) (ψ := 495907/500000) 246 152
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t49 : ((310284192629/10000000000000 : ℚ) : ℝ) ≤ stT246 49 := by
  have hc : ((217199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((310284192629/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((217199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c50 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((999259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96261/10000000) (δ := 31/2500000) (ψ := 495907/500000) 246 153
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t50 : ((1413094357517/10000000000000 : ℚ) : ℝ) ≤ stT246 50 := by
  have hc : ((999209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1413094357517/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((999209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c51 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((12267/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -214569/625000) (δ := 781/62500000) (ψ := 495907/500000) 246 154
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t51 : ((3434571777/125000000000 : ℚ) : ℝ) ≤ stT246 51 := by
  have hc : ((98111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3434571777/125000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((98111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c52 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-965869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1439787/2000000) (δ := 6207/500000000) (ψ := 495907/500000) 246 155
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t52 : ((-1339489139169/10000000000000 : ℚ) : ℝ) ≤ stT246 52 := by
  have hc : ((-965919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1339489139169/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-965919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c53 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-58329/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1128927/2500000) (δ := 6207/500000000) (ψ := 495907/500000) 246 155
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t53 : ((-80138234449/2500000000000 : ℚ) : ℝ) ≤ stT246 53 := by
  have hc : ((-116683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80138234449/2500000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-116683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c54 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((496323/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 151693/5000000) (δ := 6161/500000000) (ψ := 495907/500000) 246 156
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t54 : ((337687859223/2500000000000 : ℚ) : ℝ) ≤ stT246 54 := by
  have hc : ((248149/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((337687859223/2500000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((248149/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c55 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-1927/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4119881/10000000) (δ := 6187/500000000) (ψ := 495907/500000) 246 157
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t55 : ((-26000523/2500000000 : ℚ) : ℝ) ≤ stT246 55 := by
  have hc : ((-7713/100000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26000523/2500000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-7713/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c56 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-117119/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6961497/10000000) (δ := 12429/1000000000) (ψ := 495907/500000) 246 157
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t56 : ((-626061165807/5000000000000 : ℚ) : ℝ) ≤ stT246 56 := by
  have hc : ((-468501/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-626061165807/5000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-468501/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c57 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((65583/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2138787/10000000) (δ := 12467/1000000000) (ψ := 495907/500000) 246 158
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t57 : ((10857519937/125000000000 : ℚ) : ℝ) ≤ stT246 57 := by
  have hc : ((32789/50000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10857519937/125000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((32789/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c58 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((204569/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2873219/10000000) (δ := 309/25000000) (ψ := 495907/500000) 246 159
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t58 : ((131142267/2441406250 : ℚ) : ℝ) ≤ stT246 58 := by
  have hc : ((6392/15625 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131142267/2441406250 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((6392/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c59 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-498167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7639837/10000000) (δ := 309/25000000) (ψ := 495907/500000) 246 159
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t59 : ((-4053694893/31250000000 : ℚ) : ℝ) ≤ stT246 59 := by
  have hc : ((-31137/31250 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4053694893/31250000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-31137/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c60 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((307939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28353/125000) (δ := 12453/1000000000) (ψ := 495907/500000) 246 160
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t60 : ((99378781629/1250000000000 : ℚ) : ℝ) ≤ stT246 60 := by
  have hc : ((153957/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99378781629/1250000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((153957/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c61 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((129079/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3274203/10000000) (δ := 12457/1000000000) (ψ := 495907/500000) 246 161
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t61 : ((5163644121/156250000000 : ℚ) : ℝ) ≤ stT246 61 := by
  have hc : ((64527/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5163644121/156250000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((64527/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c62 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-112491/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1681501/2500000) (δ := 6173/500000000) (ψ := 495907/500000) 246 161
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t62 : ((-285743464989/2500000000000 : ℚ) : ℝ) ≤ stT246 62 := by
  have hc : ((-449989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285743464989/2500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-449989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c63 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((235411/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 858287/10000000) (δ := 2473/200000000) (ψ := 495907/500000) 246 162
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t63 : ((593148195157/5000000000000 : ℚ) : ℝ) ≤ stT246 63 := by
  have hc : ((470797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((593148195157/5000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((470797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c64 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-19001/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -645559/1250000) (δ := 12331/1000000000) (ψ := 495907/500000) 246 163
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t64 : ((-23753769003/400000000000 : ℚ) : ℝ) ≤ stT246 64 := by
  have hc : ((-19003/40000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23753769003/400000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-19003/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c65 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-88259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4370611/10000000) (δ := 12331/1000000000) (ψ := 495907/500000) 246 163
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t65 : ((-6843930177/312500000000 : ℚ) : ℝ) ≤ stT246 65 := by
  have hc : ((-22071/125000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6843930177/312500000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-22071/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c66 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((711521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6087/31250) (δ := 1553/125000000) (ψ := 495907/500000) 246 164
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t66 : ((437879807247/5000000000000 : ℚ) : ℝ) ≤ stT246 66 := by
  have hc : ((711471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((437879807247/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((711471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c67 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-97559/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7300469/10000000) (δ := 12379/1000000000) (ψ := 495907/500000) 246 164
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t67 : ((-5959672549/50000000000 : ℚ) : ℝ) ≤ stT246 67 := by
  have hc : ((-24391/25000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5959672549/50000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-24391/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c68 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((192127/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 43987/625000) (δ := 12317/1000000000) (ψ := 495907/500000) 246 165
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t68 : ((116488029663/1000000000000 : ℚ) : ℝ) ≤ stT246 68 := by
  have hc : ((192117/200000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116488029663/1000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((192117/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c69 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-372177/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6025909/10000000) (δ := 12393/1000000000) (ψ := 495907/500000) 246 166
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t69 : ((-224039363759/2500000000000 : ℚ) : ℝ) ≤ stT246 69 := by
  have hc : ((-186101/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224039363759/2500000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-186101/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c70 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((106833/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2823141/10000000) (δ := 1241/100000000) (ψ := 495907/500000) 246 166
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t70 : ((63837426287/1250000000000 : ℚ) : ℝ) ≤ stT246 70 := by
  have hc : ((213641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63837426287/1250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((213641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c71 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-5849/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4161293/10000000) (δ := 12303/1000000000) (ψ := 495907/500000) 246 167
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t71 : ((-27780786447/2500000000000 : ℚ) : ℝ) ≤ stT246 71 := by
  have hc : ((-46817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27780786447/2500000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-46817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c72 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-203877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2220141/5000000) (δ := 1/80000) (ψ := 495907/500000) 246 167
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t72 : ((-15020651039/625000000000 : ℚ) : ℝ) ≤ stT246 72 := by
  have hc : ((-203927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15020651039/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-203927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c73 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((220573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1392401/5000000) (δ := 1551/125000000) (ψ := 495907/500000) 246 168
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t73 : ((64532951307/1250000000000 : ℚ) : ℝ) ≤ stT246 73 := by
  have hc : ((55137/125000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64532951307/1250000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((55137/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c74 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-614901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2791321/5000000) (δ := 1551/125000000) (ψ := 495907/500000) 246 168
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t74 : ((-714866393627/10000000000000 : ℚ) : ℝ) ≤ stT246 74 := by
  have hc : ((-614951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-714866393627/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-614951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c75 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((733019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -374023/2000000) (δ := 2463/200000000) (ψ := 495907/500000) 246 169
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t75 : ((8463593043/100000000000 : ℚ) : ℝ) ≤ stT246 75 := by
  have hc : ((732969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8463593043/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((732969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c76 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-807249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6275683/10000000) (δ := 2463/200000000) (ψ := 495907/500000) 246 169
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t76 : ((-926035729621/10000000000000 : ℚ) : ℝ) ≤ stT246 76 := by
  have hc : ((-807299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-926035729621/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-807299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c77 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((53047/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1392939/10000000) (δ := 12381/1000000000) (ψ := 495907/500000) 246 170
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t77 : ((96718504271/1000000000000 : ℚ) : ℝ) ≤ stT246 77 := by
  have hc : ((424351/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96718504271/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((424351/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c78 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-432779/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1635663/2500000) (δ := 12381/1000000000) (ψ := 495907/500000) 246 170
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t78 : ((-61256805939/625000000000 : ℚ) : ℝ) ≤ stT246 78 := by
  have hc : ((-108201/125000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61256805939/625000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-108201/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c79 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((861627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -665413/5000000) (δ := 12329/1000000000) (ψ := 495907/500000) 246 171
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t79 : ((969349082199/10000000000000 : ℚ) : ℝ) ≤ stT246 79 := by
  have hc : ((861577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((969349082199/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((861577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c80 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-209179/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 400321/625000) (δ := 12329/1000000000) (ψ := 495907/500000) 246 171
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t80 : ((-233883209511/2500000000000 : ℚ) : ℝ) ≤ stT246 80 := by
  have hc : ((-418383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233883209511/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-418383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c81 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((196699/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -166299/1000000) (δ := 12367/1000000000) (ψ := 495907/500000) 246 172
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t81 : ((437081067403/5000000000000 : ℚ) : ℝ) ≤ stT246 81 := by
  have hc : ((393373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((437081067403/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((393373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c82 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-705021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2941561/5000000) (δ := 3109/250000000) (ψ := 495907/500000) 246 172
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t82 : ((-194655296609/2500000000000 : ℚ) : ℝ) ≤ stT246 82 := by
  have hc : ((-705071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194655296609/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-705071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c83 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((2333/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2370181/10000000) (δ := 12459/1000000000) (ψ := 495907/500000) 246 173
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t83 : ((400090509/6250000000 : ℚ) : ℝ) ≤ stT246 83 := by
  have hc : ((729/1250 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((400090509/6250000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((729/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c84 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-414383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 312197/625000) (δ := 3093/125000000) (ψ := 495907/500000) 246 173
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t84 : ((-45218370197/1000000000000 : ℚ) : ℝ) ≤ stT246 84 := by
  have hc : ((-414433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45218370197/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-414433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c85 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((48919/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -27477/80000) (δ := 193/15625000) (ψ := 495907/500000) 246 174
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t85 : ((26523266519/1250000000000 : ℚ) : ℝ) ≤ stT246 85 := by
  have hc : ((97813/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26523266519/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((97813/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c86 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((67379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 751683/2000000) (δ := 193/15625000) (ψ := 495907/500000) 246 174
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t86 : ((72602678583/10000000000000 : ℚ) : ℝ) ≤ stT246 86 := by
  have hc : ((67329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72602678583/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((67329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c87 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-89247/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -967919/2000000) (δ := 2489/200000000) (ψ := 495907/500000) 246 175
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t87 : ((-191392540647/5000000000000 : ℚ) : ℝ) ≤ stT246 87 := by
  have hc : ((-178519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191392540647/5000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-178519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c88 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((640519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 17102/78125) (δ := 6179/500000000) (ψ := 495907/500000) 246 175
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t88 : ((682741875407/10000000000000 : ℚ) : ℝ) ≤ stT246 88 := by
  have hc : ((640469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((682741875407/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((640469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c89 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-870929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1313943/2000000) (δ := 6169/500000000) (ψ := 495907/500000) 246 176
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t89 : ((-461617999021/5000000000000 : ℚ) : ℝ) ≤ stT246 89 := by
  have hc : ((-870979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-461617999021/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-870979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c90 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((992719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60373/2000000) (δ := 2493/200000000) (ψ := 495907/500000) 246 176
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t90 : ((261591112887/2500000000000 : ℚ) : ℝ) ≤ stT246 90 := by
  have hc : ((992669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261591112887/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((992669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c91 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-95457/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3548761/5000000) (δ := 12369/500000000) (ψ := 495907/500000) 246 176
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t91 : ((-10007138267/100000000000 : ℚ) : ℝ) ≤ stT246 91 := by
  have hc : ((-47731/50000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10007138267/100000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-47731/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c92 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((4549/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -75563/400000) (δ := 3093/250000000) (ψ := 495907/500000) 246 177
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t92 : ((18969336897/250000000000 : ℚ) : ℝ) ≤ stT246 92 := by
  have hc : ((72779/100000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18969336897/250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((72779/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c93 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-81733/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1189907/2500000) (δ := 12431/1000000000) (ψ := 495907/500000) 246 177
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t93 : ((-21191539929/625000000000 : ℚ) : ℝ) ≤ stT246 93 := by
  have hc : ((-163491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21191539929/625000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-163491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c94 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-176563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -174829/400000) (δ := 12479/1000000000) (ψ := 495907/500000) 246 178
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t94 : ((-91081266843/5000000000000 : ℚ) : ℝ) ≤ stT246 94 := by
  have hc : ((-176613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91081266843/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-176613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c95 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((656289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1068633/5000000) (δ := 3081/250000000) (ψ := 495907/500000) 246 178
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t95 : ((336643388371/5000000000000 : ℚ) : ℝ) ≤ stT246 95 := by
  have hc : ((656239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((336643388371/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((656239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c96 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-958457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -222839/312500) (δ := 97/7812500) (ψ := 495907/500000) 246 179
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t96 : ((-978272372847/10000000000000 : ℚ) : ℝ) ≤ stT246 96 := by
  have hc : ((-958507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-978272372847/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-958507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c97 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((954419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -378863/5000000) (δ := 97/7812500) (ψ := 495907/500000) 246 179
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t97 : ((484507373337/5000000000000 : ℚ) : ℝ) ≤ stT246 97 := by
  have hc : ((954369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((484507373337/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((954369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c98 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-604559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2775011/5000000) (δ := 12387/1000000000) (ψ := 495907/500000) 246 179
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t98 : ((-610747595177/10000000000000 : ℚ) : ℝ) ≤ stT246 98 := by
  have hc : ((-604609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-610747595177/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-604609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c99 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((511/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -782843/2000000) (δ := 6247/500000000) (ψ := 495907/500000) 246 180
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t99 : ((254274361/500000000000 : ℚ) : ℝ) ≤ stT246 99 := by
  have hc : ((253/50000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254274361/500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((253/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c100 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((308179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2266719/10000000) (δ := 12309/1000000000) (ψ := 495907/500000) 246 180
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t100 : ((154076845923/2500000000000 : ℚ) : ℝ) ≤ stT246 100 := by
  have hc : ((154077/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154076845923/2500000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((154077/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c101 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-61089/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1830437/2500000) (δ := 12401/1000000000) (ψ := 495907/500000) 246 181
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t101 : ((-243155943503/2500000000000 : ℚ) : ℝ) ≤ stT246 101 := by
  have hc : ((-488737/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243155943503/2500000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-488737/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c102 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((437579/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -157823/1250000) (δ := 6201/500000000) (ψ := 495907/500000) 246 181
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t102 : ((216621390219/2500000000000 : ℚ) : ℝ) ≤ stT246 102 := by
  have hc : ((218777/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216621390219/2500000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((218777/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c103 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-318523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2368709/5000000) (δ := 12401/1000000000) (ψ := 495907/500000) 246 181
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t103 : ((-31389953409/1000000000000 : ℚ) : ℝ) ≤ stT246 103 := by
  have hc : ((-318573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31389953409/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-318573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c104 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-426477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5028477/10000000) (δ := 3077/250000000) (ψ := 495907/500000) 246 182
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t104 : ((-418244272187/10000000000000 : ℚ) : ℝ) ≤ stT246 104 := by
  have hc : ((-426527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-418244272187/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-426527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c105 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((941849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 171353/2000000) (δ := 2499/200000000) (ψ := 495907/500000) 246 182
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t105 : ((9191016441/100000000000 : ℚ) : ℝ) ≤ stT246 105 := by
  have hc : ((941799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9191016441/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((941799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c106 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-446433/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3343083/5000000) (δ := 3077/250000000) (ψ := 495907/500000) 246 182
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t106 : ((-108409601247/1250000000000 : ℚ) : ℝ) ≤ stT246 106 := by
  have hc : ((-223229/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108409601247/1250000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-223229/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c107 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((67157/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -324707/1000000) (δ := 2483/200000000) (ψ := 495907/500000) 246 183
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t107 : ((8113875669/312500000000 : ℚ) : ℝ) ≤ stT246 107 := by
  have hc : ((134289/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8113875669/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((134289/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c108 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((8579/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1236953/5000000) (δ := 2483/200000000) (ψ := 495907/500000) 246 183
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t108 : ((1056562047/20000000000 : ℚ) : ℝ) ≤ stT246 108 := by
  have hc : ((274503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1056562047/20000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((274503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c109 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-496683/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7565849/10000000) (δ := 39/3125000) (ψ := 495907/500000) 246 184
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t109 : ((-118940083379/1250000000000 : ℚ) : ℝ) ≤ stT246 109 := by
  have hc : ((-124177/125000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118940083379/1250000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-124177/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c110 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((711093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1949361/10000000) (δ := 12323/1000000000) (ψ := 495907/500000) 246 184
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t110 : ((338976240433/5000000000000 : ℚ) : ℝ) ≤ stT246 110 := by
  have hc : ((711043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((338976240433/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((711043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c111 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((61973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3616327/10000000) (δ := 39/3125000) (ψ := 495907/500000) 246 184
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t111 : ((14699594459/1250000000000 : ℚ) : ℝ) ≤ stT246 111 := by
  have hc : ((15487/125000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14699594459/1250000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((15487/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c112 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-872151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6575947/10000000) (δ := 12373/1000000000) (ψ := 495907/500000) 246 185
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t112 : ((-51509574457/625000000000 : ℚ) : ℝ) ≤ stT246 112 := by
  have hc : ((-872201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51509574457/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-872201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c113 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((112897/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -277303/2500000) (δ := 12373/1000000000) (ψ := 495907/500000) 246 185
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t113 : ((5309929317/62500000000 : ℚ) : ℝ) ≤ stT246 113 := by
  have hc : ((451563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5309929317/62500000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((451563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c114 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-152331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4309307/10000000) (δ := 12373/1000000000) (ψ := 495907/500000) 246 185
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t114 : ((-71358955633/5000000000000 : ℚ) : ℝ) ≤ stT246 114 := by
  have hc : ((-152381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71358955633/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-152381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c115 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-744761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6027431/10000000) (δ := 6233/500000000) (ψ := 495907/500000) 246 186
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t115 : ((-138907996311/2000000000000 : ℚ) : ℝ) ≤ stT246 115 := by
  have hc : ((-744811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138907996311/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-744811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c116 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((3843/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -702761/10000000) (δ := 6233/500000000) (ψ := 495907/500000) 246 186
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t116 : ((2229967233/25000000000 : ℚ) : ℝ) ≤ stT246 116 := by
  have hc : ((9607/10000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2229967233/25000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((9607/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c117 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-64201/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1144069/2500000) (δ := 6233/500000000) (ψ := 495907/500000) 246 186
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t117 : ((-118730889927/5000000000000 : ℚ) : ℝ) ≤ stT246 117 := by
  have hc : ((-128427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118730889927/5000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-128427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c118 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-354559/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2948803/5000000) (δ := 3111/250000000) (ψ := 495907/500000) 246 187
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t118 : ((-1632105829/25000000000 : ℚ) : ℝ) ≤ stT246 118 := by
  have hc : ((-44323/62500 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1632105829/25000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-44323/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c119 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((192039/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -22117/312500) (δ := 3111/250000000) (ψ := 495907/500000) 246 187
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t119 : ((88016300121/1000000000000 : ℚ) : ℝ) ≤ stT246 119 := by
  have hc : ((192029/200000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88016300121/1000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((192029/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c120 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-203281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 110969/250000) (δ := 12359/1000000000) (ψ := 495907/500000) 246 187
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t120 : ((-185614973301/10000000000000 : ℚ) : ℝ) ≤ stT246 120 := by
  have hc : ((-203331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185614973301/10000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-203331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c121 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-780447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6165441/10000000) (δ := 12351/1000000000) (ψ := 495907/500000) 246 188
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t121 : ((-709542798227/10000000000000 : ℚ) : ℝ) ≤ stT246 121 := by
  have hc : ((-780497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-709542798227/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-780497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c122 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((904123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -275921/2500000) (δ := 3113/250000000) (ψ := 495907/500000) 246 188
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t122 : ((818508819061/10000000000000 : ℚ) : ℝ) ≤ stT246 122 := by
  have hc : ((904073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((818508819061/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((904073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c123 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((2049/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1958373/5000000) (δ := 12351/1000000000) (ψ := 495907/500000) 246 188
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t123 : ((228122257/625000000000 : ℚ) : ℝ) ≤ stT246 123 := by
  have hc : ((253/62500 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228122257/625000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((253/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c124 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-914301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6811439/10000000) (δ := 6229/500000000) (ψ := 495907/500000) 246 189
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t124 : ((-821111885477/10000000000000 : ℚ) : ℝ) ≤ stT246 124 := by
  have hc : ((-914351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-821111885477/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-914351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c125 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((146521/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -467909/2500000) (δ := 6229/500000000) (ψ := 495907/500000) 246 189
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t125 : ((131043394197/2000000000000 : ℚ) : ℝ) ≤ stT246 125 := by
  have hc : ((146511/200000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131043394197/2000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((146511/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c126 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((175797/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3028807/10000000) (δ := 6229/500000000) (ψ := 495907/500000) 246 189
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t126 : ((3914750041/125000000000 : ℚ) : ℝ) ≤ stT246 126 := by
  have hc : ((43943/125000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3914750041/125000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((43943/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c127 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-499947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -97719/125000) (δ := 6183/500000000) (ψ := 495907/500000) 246 190
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t127 : ((-110913413501/1250000000000 : ℚ) : ℝ) ≤ stT246 127 := by
  have hc : ((-124993/125000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110913413501/1250000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-124993/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c128 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((364611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -93561/312500) (δ := 6183/500000000) (ψ := 495907/500000) 246 190
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t128 : ((322229270363/10000000000000 : ℚ) : ℝ) ≤ stT246 128 := by
  have hc : ((364561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((322229270363/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((364561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c129 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((150777/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1792101/10000000) (δ := 6183/500000000) (ψ := 495907/500000) 246 190
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t129 : ((2654856103/40000000000 : ℚ) : ℝ) ≤ stT246 129 := by
  have hc : ((150767/200000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2654856103/40000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((150767/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c130 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-432627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6541131/10000000) (δ := 6183/500000000) (ψ := 495907/500000) 246 190
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t130 : ((-94865332617/1250000000000 : ℚ) : ℝ) ≤ stT246 130 := by
  have hc : ((-108163/125000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94865332617/1250000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-108163/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c131 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-26163/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4454149/10000000) (δ := 1233/100000000) (ψ := 495907/500000) 246 191
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t131 : ((-18291363657/1000000000000 : ℚ) : ℝ) ≤ stT246 131 := by
  have hc : ((-104677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18291363657/1000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-104677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c132 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((249009/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5567/250000) (δ := 1233/100000000) (ψ := 495907/500000) 246 191
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t132 : ((108361782821/1250000000000 : ℚ) : ℝ) ≤ stT246 132 := by
  have hc : ((497993/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108361782821/1250000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((497993/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c133 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-366167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 304013/625000) (δ := 1233/100000000) (ψ := 495907/500000) 246 191
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t133 : ((-31755042287/1000000000000 : ℚ) : ℝ) ≤ stT246 133 := by
  have hc : ((-366217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31755042287/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-366217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c134 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-399011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1247401/2000000) (δ := 1239/50000000) (ψ := 495907/500000) 246 192
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t134 : ((-86178707571/1250000000000 : ℚ) : ℝ) ≤ stT246 134 := by
  have hc : ((-99759/125000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86178707571/1250000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-99759/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c135 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((39321/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1664511/10000000) (δ := 619/50000000) (ψ := 495907/500000) 246 192
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t135 : ((33839938847/500000000000 : ℚ) : ℝ) ≤ stT246 135 := by
  have hc : ((78637/100000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33839938847/500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((78637/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c136 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((408761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11497/40000) (δ := 12423/1000000000) (ψ := 495907/500000) 246 192
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t136 : ((87616603203/2500000000000 : ℚ) : ℝ) ≤ stT246 136 := by
  have hc : ((408711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87616603203/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((408711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c137 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-491033/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3689901/5000000) (δ := 619/50000000) (ψ := 495907/500000) 246 192
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t137 : ((-104884832691/1250000000000 : ℚ) : ℝ) ≤ stT246 137 := by
  have hc : ((-245529/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104884832691/1250000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-245529/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c138 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((7153/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3855451/10000000) (δ := 3079/250000000) (ψ := 495907/500000) 246 193
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t138 : ((1519598367/625000000000 : ℚ) : ℝ) ≤ stT246 138 := by
  have hc : ((14281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1519598367/625000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((14281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c139 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((121593/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 292517/5000000) (δ := 12487/1000000000) (ψ := 495907/500000) 246 193
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t139 : ((103128422309/1250000000000 : ℚ) : ℝ) ≤ stT246 139 := by
  have hc : ((486347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103128422309/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((486347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c140 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-5173/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4993661/10000000) (δ := 3079/250000000) (ψ := 495907/500000) 246 193
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t140 : ((-6996024059/200000000000 : ℚ) : ℝ) ≤ stT246 140 := by
  have hc : ((-41389/100000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6996024059/200000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-41389/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c141 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-12836/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6337101/10000000) (δ := 6197/500000000) (ψ := 495907/500000) 246 194
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t141 : ((-43242084013/625000000000 : ℚ) : ℝ) ≤ stT246 141 := by
  have hc : ((-410777/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43242084013/625000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-410777/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c142 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((13987/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1990773/10000000) (δ := 6197/500000000) (ψ := 495907/500000) 246 194
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t142 : ((5868392733/100000000000 : ℚ) : ℝ) ≤ stT246 142 := by
  have hc : ((6993/10000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5868392733/100000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((6993/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c143 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((298909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2325051/10000000) (δ := 6197/500000000) (ψ := 495907/500000) 246 194
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t143 : ((31242419241/625000000000 : ℚ) : ℝ) ≤ stT246 143 := by
  have hc : ((74721/125000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31242419241/625000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((74721/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c144 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-7031/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 330537/500000) (δ := 6197/500000000) (ψ := 495907/500000) 246 194
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t144 : ((-14648761719/200000000000 : ℚ) : ℝ) ≤ stT246 144 := by
  have hc : ((-35157/40000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14648761719/200000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-35157/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c145 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-89389/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1210279/2500000) (δ := 6151/500000000) (ψ := 495907/500000) 246 195
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t145 : ((-29697569073/1000000000000 : ℚ) : ℝ) ≤ stT246 145 := by
  have hc : ((-178803/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29697569073/1000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-178803/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c146 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((242491/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -614283/10000000) (δ := 12501/1000000000) (ψ := 495907/500000) 246 195
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t146 : ((80270567597/1000000000000 : ℚ) : ℝ) ≤ stT246 146 := by
  have hc : ((484957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80270567597/1000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((484957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c147 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((136907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1791823/5000000) (δ := 6151/500000000) (ψ := 495907/500000) 246 195
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t147 : ((56438868801/5000000000000 : ℚ) : ℝ) ≤ stT246 147 := by
  have hc : ((136857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56438868801/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((136857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c148 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-999187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7753161/10000000) (δ := 12501/1000000000) (ψ := 495907/500000) 246 195
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t148 : ((-164273563563/2000000000000 : ℚ) : ℝ) ≤ stT246 148 := by
  have hc : ((-999237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164273563563/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-999237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c149 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((45449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -381333/1000000) (δ := 12409/1000000000) (ψ := 495907/500000) 246 196
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t149 : ((37192268169/10000000000000 : ℚ) : ℝ) ≤ stT246 149 := by
  have hc : ((45399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37192268169/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((45399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c150 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((124099/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 300343/10000000) (δ := 6197/500000000) (ψ := 495907/500000) 246 196
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t150 : ((25330308501/312500000000 : ℚ) : ℝ) ≤ stT246 150 := by
  have hc : ((496371/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25330308501/312500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((496371/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c151 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-182877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1096693/2500000) (δ := 6197/500000000) (ψ := 495907/500000) 246 196
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t151 : ((-148863980403/10000000000000 : ℚ) : ℝ) ≤ stT246 151 := by
  have hc : ((-182927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148863980403/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-182927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c152 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-972073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7261761/10000000) (δ := 12487/1000000000) (ψ := 495907/500000) 246 197
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t152 : ((-197124185571/2500000000000 : ℚ) : ℝ) ≤ stT246 152 := by
  have hc : ((-972123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-197124185571/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-972123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c153 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((275599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20181/62500) (δ := 12487/1000000000) (ψ := 495907/500000) 246 197
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t153 : ((55692035037/2500000000000 : ℚ) : ℝ) ≤ stT246 153 := by
  have hc : ((275549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55692035037/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((275549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c154 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((476009/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 777581/10000000) (δ := 3079/250000000) (ψ := 495907/500000) 246 197
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t154 : ((11986199339/156250000000 : ℚ) : ℝ) ≤ stT246 154 := by
  have hc : ((29749/31250 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11986199339/156250000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((29749/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c155 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-16319/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 594771/1250000) (δ := 12487/1000000000) (ψ := 495907/500000) 246 197
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t155 : ((-1310975523/50000000000 : ℚ) : ℝ) ≤ stT246 155 := by
  have hc : ((-32643/100000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1310975523/50000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-32643/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c156 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-470761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6994791/10000000) (δ := 12423/1000000000) (ψ := 495907/500000) 246 198
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t156 : ((-188465286913/2500000000000 : ℚ) : ℝ) ≤ stT246 156 := by
  have hc : ((-235393/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188465286913/2500000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-235393/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c157 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((337981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -383133/1250000) (δ := 12423/1000000000) (ψ := 495907/500000) 246 198
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t157 : ((134849000033/5000000000000 : ℚ) : ℝ) ≤ stT246 157 := by
  have hc : ((337931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134849000033/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((337931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c158 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((944121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 419847/5000000) (δ := 12423/1000000000) (ψ := 495907/500000) 246 198
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t158 : ((751062292547/10000000000000 : ℚ) : ℝ) ≤ stT246 158 := by
  have hc : ((944071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((751062292547/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((944071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c159 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-62371/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1179963/2500000) (δ := 12423/1000000000) (ψ := 495907/500000) 246 198
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t159 : ((-12367844203/500000000000 : ℚ) : ℝ) ≤ stT246 159 := by
  have hc : ((-62381/200000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12367844203/500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-62381/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c160 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-29957/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1783077/2500000) (δ := 12473/1000000000) (ψ := 495907/500000) 246 199
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t160 : ((-37894945209/500000000000 : ℚ) : ℝ) ≤ stT246 160 := by
  have hc : ((-479337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37894945209/500000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-479337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c161 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((123981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -66011/200000) (δ := 1233/100000000) (ψ := 495907/500000) 246 199
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t161 : ((2442274079/125000000000 : ℚ) : ℝ) ≤ stT246 161 := by
  have hc : ((30989/125000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2442274079/125000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((30989/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c162 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((122433/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50753/1000000) (δ := 1233/100000000) (ψ := 495907/500000) 246 199
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t162 : ((192375028759/2500000000000 : ℚ) : ℝ) ≤ stT246 162 := by
  have hc : ((489707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192375028759/2500000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((489707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c163 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-36389/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2146089/5000000) (δ := 12473/1000000000) (ψ := 495907/500000) 246 199
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t163 : ((-57023750583/5000000000000 : ℚ) : ℝ) ≤ stT246 163 := by
  have hc : ((-72803/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57023750583/5000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-72803/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c164 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-996813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3827161/5000000) (δ := 6183/500000000) (ψ := 495907/500000) 246 200
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t164 : ((-778419413947/10000000000000 : ℚ) : ℝ) ≤ stT246 164 := by
  have hc : ((-996863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-778419413947/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-996863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c165 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((2251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3915737/10000000) (δ := 6183/500000000) (ψ := 495907/500000) 246 200
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t165 : ((433234137/1250000000000 : ℚ) : ℝ) ≤ stT246 165 := by
  have hc : ((1113/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((433234137/1250000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((1113/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c166 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((996811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -99861/5000000) (δ := 12437/1000000000) (ψ := 495907/500000) 246 200
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t166 : ((15472721003/200000000000 : ℚ) : ℝ) ≤ stT246 166 := by
  have hc : ((996761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15472721003/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((996761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c167 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((1077/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3494029/10000000) (δ := 6183/500000000) (ψ := 495907/500000) 246 200
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t167 : ((13330648821/1000000000000 : ℚ) : ℝ) ≤ stT246 167 := by
  have hc : ((17227/100000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13330648821/1000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((17227/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c168 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-481167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7165641/10000000) (δ := 12437/1000000000) (ψ := 495907/500000) 246 200
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t168 : ((-46405976033/625000000000 : ℚ) : ℝ) ≤ stT246 168 := by
  have hc : ((-60149/62500 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46405976033/625000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-60149/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c169 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-75329/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4892421/10000000) (δ := 6229/500000000) (ψ := 495907/500000) 246 201
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t169 : ((-57953094309/2000000000000 : ℚ) : ℝ) ≤ stT246 169 := by
  have hc : ((-75339/200000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57953094309/2000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-75339/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c170 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((54679/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -252821/2000000) (δ := 2469/200000000) (ψ := 495907/500000) 246 201
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t170 : ((83868855587/1250000000000 : ℚ) : ℝ) ≤ stT246 170 := by
  have hc : ((437407/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83868855587/1250000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((437407/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c171 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((592069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2342931/10000000) (δ := 6229/500000000) (ψ := 495907/500000) 246 201
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t171 : ((452728177661/10000000000000 : ℚ) : ℝ) ≤ stT246 171 := by
  have hc : ((592019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((452728177661/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((592019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c172 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-358949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1185787/2000000) (δ := 2469/200000000) (ψ := 495907/500000) 246 201
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t172 : ((-136857581091/2500000000000 : ℚ) : ℝ) ≤ stT246 172 := by
  have hc : ((-179487/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136857581091/2500000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-179487/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c173 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-792397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1553453/2500000) (δ := 12351/1000000000) (ψ := 495907/500000) 246 202
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t173 : ((-301243179921/5000000000000 : ℚ) : ℝ) ≤ stT246 173 := by
  have hc : ((-792447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-301243179921/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-792447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c174 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((24109/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -166821/625000) (δ := 3113/250000000) (ψ := 495907/500000) 246 202
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t174 : ((18275089437/500000000000 : ℚ) : ℝ) ≤ stT246 174 := by
  have hc : ((48213/100000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18275089437/500000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((48213/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c175 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((942053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 213811/2500000) (δ := 12351/1000000000) (ψ := 495907/500000) 246 202
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t175 : ((89010805473/1250000000000 : ℚ) : ℝ) ≤ stT246 175 := by
  have hc : ((942003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89010805473/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((942003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c176 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-172147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2179757/5000000) (δ := 12351/1000000000) (ψ := 495907/500000) 246 202
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t176 : ((-129798482463/10000000000000 : ℚ) : ℝ) ≤ stT246 176 := by
  have hc : ((-172197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129798482463/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-172197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c177 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-124999/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7843981/10000000) (δ := 12351/1000000000) (ψ := 495907/500000) 246 202
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t177 : ((-375839284587/5000000000000 : ℚ) : ℝ) ≤ stT246 177 := by
  have hc : ((-500021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-375839284587/5000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-500021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c178 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-187761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -879839/2000000) (δ := 12359/1000000000) (ψ := 495907/500000) 246 203
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t178 : ((-35192588613/2500000000000 : ℚ) : ℝ) ≤ stT246 178 := by
  have hc : ((-187811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35192588613/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-187811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c179 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((928103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -953781/10000000) (δ := 3111/250000000) (ψ := 495907/500000) 246 203
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t179 : ((138731858811/2000000000000 : ℚ) : ℝ) ≤ stT246 179 := by
  have hc : ((928053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138731858811/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((928053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c180 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((137391/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38631/156250) (δ := 3111/250000000) (ψ := 495907/500000) 246 203
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t180 : ((40958300747/1000000000000 : ℚ) : ℝ) ≤ stT246 180 := by
  have hc : ((274757/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40958300747/1000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((274757/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c181 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-704023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5879607/10000000) (δ := 3111/250000000) (ψ := 495907/500000) 246 203
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t181 : ((-104666788107/2000000000000 : ℚ) : ℝ) ≤ stT246 181 := by
  have hc : ((-704073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104666788107/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-704073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c182 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-844261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -402497/625000) (δ := 12337/1000000000) (ψ := 495907/500000) 246 204
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t182 : ((-500676423/8000000000 : ℚ) : ℝ) ≤ stT246 182 := by
  have hc : ((-844311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-500676423/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-844311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c183 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((3361/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3070059/10000000) (δ := 6233/500000000) (ψ := 495907/500000) 246 204
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t183 : ((4968304341/200000000000 : ℚ) : ℝ) ≤ stT246 183 := by
  have hc : ((6721/20000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4968304341/200000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((6721/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c184 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((99367/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56289/2000000) (δ := 6233/500000000) (ψ := 495907/500000) 246 204
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t184 : ((36625280329/500000000000 : ℚ) : ℝ) ≤ stT246 184 := by
  have hc : ((49681/50000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36625280329/500000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((49681/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c185 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((2491/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1807403/5000000) (δ := 12337/1000000000) (ψ := 495907/500000) 246 204
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t185 : ((91534143/10000000000 : ℚ) : ℝ) ≤ stT246 185 := by
  have hc : ((249/2000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91534143/10000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((249/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c186 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-58281/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1732537/2500000) (δ := 12337/1000000000) (ψ := 495907/500000) 246 204
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t186 : ((-85472037357/1250000000000 : ℚ) : ℝ) ≤ stT246 186 := by
  have hc : ((-466273/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85472037357/1250000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-466273/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c187 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-23283/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1096037/2000000) (δ := 12373/1000000000) (ψ := 495907/500000) 246 205
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t187 : ((-3405538361/80000000000 : ℚ) : ℝ) ≤ stT246 187 := by
  have hc : ((-4657/8000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3405538361/80000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-4657/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c188 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((19909/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1100103/5000000) (δ := 1243/100000000) (ψ := 495907/500000) 246 205
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t188 : ((58075887789/1250000000000 : ℚ) : ℝ) ≤ stT246 188 := by
  have hc : ((318519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58075887789/1250000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((318519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c189 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((18221/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1062431/10000000) (δ := 12373/1000000000) (ψ := 495907/500000) 246 205
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t189 : ((20707941/312500000 : ℚ) : ℝ) ≤ stT246 189 := by
  have hc : ((911/1000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20707941/312500000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((911/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c190 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-15173/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2153893/5000000) (δ := 12373/1000000000) (ψ := 495907/500000) 246 205
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t190 : ((-5505644953/500000000000 : ℚ) : ℝ) ≤ stT246 190 := by
  have hc : ((-7589/50000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5505644953/500000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-7589/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c191 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-99193/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7536167/10000000) (δ := 12373/1000000000) (ψ := 495907/500000) 246 205
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t191 : ((-1435543857/20000000000 : ℚ) : ℝ) ≤ stT246 191 := by
  have hc : ((-49599/50000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1435543857/20000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-49599/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c192 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-200833/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -620041/1250000) (δ := 12323/1000000000) (ψ := 495907/500000) 246 206
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t192 : ((-9059800519/312500000000 : ℚ) : ℝ) ≤ stT246 192 := by
  have hc : ((-100429/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9059800519/312500000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-100429/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c193 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((760827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -882763/5000000) (δ := 12323/1000000000) (ψ := 495907/500000) 246 206
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t193 : ((109523739251/2000000000000 : ℚ) : ℝ) ≤ stT246 193 := by
  have hc : ((760777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109523739251/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((760777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c194 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((422263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 706397/5000000) (δ := 12323/1000000000) (ψ := 495907/500000) 246 206
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t194 : ((75787287501/1250000000000 : ℚ) : ℝ) ≤ stT246 194 := by
  have hc : ((211119/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75787287501/1250000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((211119/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c195 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-32027/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 914951/2000000) (δ := 12323/1000000000) (ψ := 495907/500000) 246 206
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t195 : ((-18351592659/1000000000000 : ℚ) : ℝ) ≤ stT246 195 := by
  have hc : ((-128133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18351592659/1000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-128133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c196 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-62411/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3860271/5000000) (δ := 39/3125000) (ψ := 495907/500000) 246 206
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t196 : ((-178326142759/2500000000000 : ℚ) : ℝ) ≤ stT246 196 := by
  have hc : ((-499313/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178326142759/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-499313/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c197 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-90929/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -38861/80000) (δ := 3097/250000000) (ψ := 495907/500000) 246 207
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t197 : ((-129586362893/5000000000000 : ℚ) : ℝ) ≤ stT246 197 := by
  have hc : ((-181883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129586362893/5000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-181883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c198 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((11976/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -108981/625000) (δ := 2483/200000000) (ψ := 495907/500000) 246 207
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t198 : ((272333335483/5000000000000 : ℚ) : ℝ) ≤ stT246 198 := by
  have hc : ((383207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272333335483/5000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((383207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c199 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((856771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1354551/10000000) (δ := 2483/200000000) (ψ := 495907/500000) 246 207
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t199 : ((607313239201/10000000000000 : ℚ) : ℝ) ≤ stT246 199 := by
  have hc : ((856721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((607313239201/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((856721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c200 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-40537/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4437239/10000000) (δ := 3097/250000000) (ψ := 495907/500000) 246 207
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t200 : ((-28671067529/2000000000000 : ℚ) : ℝ) ≤ stT246 200 := by
  have hc : ((-40547/200000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28671067529/2000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-40547/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c201 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-990251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7504613/10000000) (δ := 3097/250000000) (ψ := 495907/500000) 246 207
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t201 : ((-349252424573/5000000000000 : ℚ) : ℝ) ≤ stT246 201 := by
  have hc : ((-990301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-349252424573/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-990301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c202 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-470379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -515129/1000000) (δ := 3077/250000000) (ψ := 495907/500000) 246 208
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t202 : ((-165496451771/5000000000000 : ℚ) : ℝ) ≤ stT246 202 := by
  have hc : ((-470429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165496451771/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-470429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c203 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((165803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -422847/2000000) (δ := 2499/200000000) (ψ := 495907/500000) 246 208
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t203 : ((116362051911/2500000000000 : ℚ) : ℝ) ≤ stT246 203 := by
  have hc : ((331581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116362051911/2500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((331581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c204 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((934783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7263/80000) (δ := 2499/200000000) (ψ := 495907/500000) 246 208
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t204 : ((32722198131/500000000000 : ℚ) : ℝ) ≤ stT246 204 := by
  have hc : ((934733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32722198131/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((934733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c205 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((2353/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156609/400000) (δ := 2499/200000000) (ψ := 495907/500000) 246 208
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t205 : ((20324313/62500000000 : ℚ) : ℝ) ≤ stT246 205 := by
  have hc : ((291/62500 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20324313/62500000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((291/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c206 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-3717/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3453969/5000000) (δ := 2499/200000000) (ψ := 495907/500000) 246 208
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t206 : ((-3237374531/50000000000 : ℚ) : ℝ) ≤ stT246 206 := by
  have hc : ((-9293/10000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3237374531/50000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-9293/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c207 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-687423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5821827/10000000) (δ := 12401/1000000000) (ψ := 495907/500000) 246 209
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t207 : ((-477827421177/10000000000000 : ℚ) : ℝ) ≤ stT246 207 := by
  have hc : ((-687473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-477827421177/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-687473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c208 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((4147/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2857957/10000000) (δ := 6201/500000000) (ψ := 495907/500000) 246 209
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t208 : ((46001271/1600000000 : ℚ) : ℝ) ≤ stT246 208 := by
  have hc : ((8293/20000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46001271/1600000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((8293/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c209 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((999327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45853/5000000) (δ := 6201/500000000) (ψ := 495907/500000) 246 209
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t209 : ((345606945389/5000000000000 : ℚ) : ℝ) ≤ stT246 209 := by
  have hc : ((999277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((345606945389/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((999277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c210 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((88041/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 605457/2000000) (δ := 12401/1000000000) (ψ := 495907/500000) 246 209
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t210 : ((24298154741/1000000000000 : ℚ) : ℝ) ≤ stT246 210 := by
  have hc : ((176057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24298154741/1000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((176057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c211 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-144687/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 743613/1250000) (δ := 12401/1000000000) (ψ := 495907/500000) 246 209
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t211 : ((-99613611013/2000000000000 : ℚ) : ℝ) ≤ stT246 211 := by
  have hc : ((-144697/200000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99613611013/2000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-144697/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c212 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-920639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3425639/5000000) (δ := 6247/500000000) (ψ := 495907/500000) 246 210
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t212 : ((-632331967267/10000000000000 : ℚ) : ℝ) ≤ stT246 212 := by
  have hc : ((-920689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-632331967267/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-920689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c213 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-12063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3957149/10000000) (δ := 12309/1000000000) (ψ := 495907/500000) 246 210
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t213 : ((-8299694357/10000000000000 : ℚ) : ℝ) ≤ stT246 213 := by
  have hc : ((-12113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8299694357/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-12113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c214 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((908707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1076551/10000000) (δ := 6247/500000000) (ψ := 495907/500000) 246 210
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t214 : ((124228859069/2000000000000 : ℚ) : ℝ) ≤ stT246 214 := by
  have hc : ((908657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124228859069/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((908657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c215 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((150857/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1790579/10000000) (δ := 6247/500000000) (ψ := 495907/500000) 246 210
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t215 : ((51438374459/1000000000000 : ℚ) : ℝ) ≤ stT246 215 := by
  have hc : ((150847/200000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51438374459/1000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((150847/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c216 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-283051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 185777/400000) (δ := 6247/500000000) (ψ := 495907/500000) 246 210
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t216 : ((-96312941907/5000000000000 : ℚ) : ℝ) ≤ stT246 216 := by
  have hc : ((-283101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96312941907/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-283101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c217 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-989131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7485049/10000000) (δ := 12309/1000000000) (ψ := 495907/500000) 246 210
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t217 : ((-134300115189/2000000000000 : ℚ) : ℝ) ≤ stT246 217 := by
  have hc : ((-989181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134300115189/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-989181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c218 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-110829/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5395329/10000000) (δ := 12387/1000000000) (ψ := 495907/500000) 246 211
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t218 : ((-37534851477/1000000000000 : ℚ) : ℝ) ≤ stT246 218 := by
  have hc : ((-110839/200000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37534851477/1000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-110839/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c219 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((512877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1290329/5000000) (δ := 97/7812500) (ψ := 495907/500000) 246 211
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t219 : ((346536178499/10000000000000 : ℚ) : ℝ) ≤ stT246 219 := by
  have hc : ((512827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((346536178499/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((512827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c220 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((99609/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 221159/10000000) (δ := 97/7812500) (ψ := 495907/500000) 246 211
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t220 : ((16788229299/250000000000 : ℚ) : ℝ) ≤ stT246 220 := by
  have hc : ((24901/25000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16788229299/250000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((24901/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c221 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((22407/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3010307/10000000) (δ := 97/7812500) (ψ := 495907/500000) 246 211
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t221 : ((3767614851/156250000000 : ℚ) : ℝ) ≤ stT246 221 := by
  have hc : ((179231/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3767614851/156250000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((179231/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c222 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-84647/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2893393/5000000) (δ := 97/7812500) (ψ := 495907/500000) 246 211
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t222 : ((-227262485241/5000000000000 : ℚ) : ℝ) ≤ stT246 222 := by
  have hc : ((-338613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-227262485241/5000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-338613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c223 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-480701/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3578561/5000000) (δ := 12479/1000000000) (ψ := 495907/500000) 246 212
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t223 : ((-3219181659/50000000000 : ℚ) : ℝ) ≤ stT246 223 := by
  have hc : ((-240363/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3219181659/50000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-240363/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c224 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-2972/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4405427/10000000) (δ := 3081/250000000) (ψ := 495907/500000) 246 212
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t224 : ((-31780410933/2500000000000 : ℚ) : ℝ) ≤ stT246 224 := by
  have hc : ((-95129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31780410933/2500000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-95129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c225 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((786059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1665971/10000000) (δ := 3081/250000000) (ψ := 495907/500000) 246 212
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t225 : ((262002737997/5000000000000 : ℚ) : ℝ) ≤ stT246 225 := by
  have hc : ((786009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((262002737997/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((786009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c226 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((22781/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1061277/10000000) (δ := 24679/1000000000) (ψ := 495907/500000) 246 212
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t226 : ((6061144761/100000000000 : ℚ) : ℝ) ≤ stT246 226 := by
  have hc : ((91119/100000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6061144761/100000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((91119/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c227 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((60147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3776533/10000000) (δ := 3081/250000000) (ψ := 495907/500000) 246 212
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t227 : ((39887761131/10000000000000 : ℚ) : ℝ) ≤ stT246 227 := by
  have hc : ((60097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39887761131/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((60097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c228 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-852701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6479827/10000000) (δ := 3081/250000000) (ψ := 495907/500000) 246 212
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t228 : ((-564748846517/10000000000000 : ℚ) : ℝ) ≤ stT246 228 := by
  have hc : ((-852751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-564748846517/10000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-852751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c229 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-432177/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -130733/200000) (δ := 12431/1000000000) (ψ := 495907/500000) 246 213
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t229 : ((-142803646719/2500000000000 : ℚ) : ℝ) ≤ stT246 229 := by
  have hc : ((-216101/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142803646719/2500000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-216101/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c230 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((7007/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3856911/10000000) (δ := 3093/250000000) (ψ := 495907/500000) 246 213
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t230 : ((461203341/250000000000 : ℚ) : ℝ) ≤ stT246 230 := by
  have hc : ((13989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((461203341/250000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((13989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c231 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((27783/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -237759/2000000) (δ := 3093/250000000) (ψ := 495907/500000) 246 213
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t231 : ((292461193353/5000000000000 : ℚ) : ℝ) ≤ stT246 231 := by
  have hc : ((444503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292461193353/5000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((444503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c232 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((832549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1467759/10000000) (δ := 3093/250000000) (ψ := 495907/500000) 246 213
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t232 : ((136640558367/2500000000000 : ℚ) : ℝ) ≤ stT246 232 := by
  have hc : ((832499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136640558367/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((832499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c233 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-7431/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 514117/1250000) (δ := 12431/1000000000) (ψ := 495907/500000) 246 213
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t233 : ((-608935899/125000000000 : ℚ) : ℝ) ≤ stT246 233 := by
  have hc : ((-1859/25000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-608935899/125000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-1859/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c234 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-225881/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1686699/2500000) (δ := 3093/250000000) (ψ := 495907/500000) 246 213
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t234 : ((-295342649427/5000000000000 : ℚ) : ℝ) ≤ stT246 234 := by
  have hc : ((-451787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-295342649427/5000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-451787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c235 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-821837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6338561/10000000) (δ := 6169/500000000) (ψ := 495907/500000) 246 214
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t235 : ((-536140724823/10000000000000 : ℚ) : ℝ) ≤ stT246 235 := by
  have hc : ((-821887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-536140724823/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-821887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c236 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((19969/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3727087/10000000) (δ := 2493/200000000) (ψ := 495907/500000) 246 214
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t236 : ((405955123/78125000000 : ℚ) : ℝ) ≤ stT246 236 := by
  have hc : ((39913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((405955123/78125000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((39913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c237 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((450077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -563341/5000000) (δ := 6169/500000000) (ψ := 495907/500000) 246 214
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t237 : ((73084956897/1250000000000 : ℚ) : ℝ) ≤ stT246 237 := by
  have hc : ((112513/125000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73084956897/1250000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((112513/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c238 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((833651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58511/400000) (δ := 2493/200000000) (ψ := 495907/500000) 246 214
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t238 : ((540342669003/10000000000000 : ℚ) : ℝ) ≤ stT246 238 := by
  have hc : ((833601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((540342669003/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((833601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c239 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-45751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4041409/10000000) (δ := 6169/500000000) (ψ := 495907/500000) 246 214
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t239 : ((-29626239447/10000000000000 : ℚ) : ℝ) ≤ stT246 239 := by
  have hc : ((-45801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29626239447/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-45801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c240 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-878597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10327/15625) (δ := 6169/500000000) (ψ := 495907/500000) 246 214
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t240 : ((-283582440603/5000000000000 : ℚ) : ℝ) ≤ stT246 240 := by
  have hc : ((-878647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283582440603/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-878647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c241 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-86533/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6541513/10000000) (δ := 2489/200000000) (ψ := 495907/500000) 246 215
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t241 : ((-27872029233/500000000000 : ℚ) : ℝ) ≤ stT246 241 := by
  have hc : ((-43269/50000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27872029233/500000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-43269/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c242 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-27169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3994921/10000000) (δ := 2489/200000000) (ψ := 495907/500000) 246 215
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t242 : ((-699882147/400000000000 : ℚ) : ℝ) ≤ stT246 242 := by
  have hc : ((-27219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-699882147/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-27219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c243 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((417259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -729423/5000000) (δ := 6179/500000000) (ψ := 495907/500000) 246 215
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t243 : ((267655611/5000000000 : ℚ) : ℝ) ≤ stT246 243 := by
  have hc : ((208617/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267655611/5000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((208617/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c244 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((455161/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 266709/2500000) (δ := 6179/500000000) (ψ := 495907/500000) 246 215
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t244 : ((1138167129/19531250000 : ℚ) : ℝ) ≤ stT246 244 := by
  have hc : ((14223/15625 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1138167129/19531250000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((14223/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c245 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((137497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 716431/2000000) (δ := 12379/500000000) (ψ := 495907/500000) 246 215
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t245 : ((21952897393/2500000000000 : ℚ) : ℝ) ≤ stT246 245 := by
  have hc : ((137447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21952897393/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((137447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c246 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-380259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3043633/5000000) (δ := 2489/200000000) (ψ := 495907/500000) 246 215
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t246 : ((-60615082967/1250000000000 : ℚ) : ℝ) ≤ stT246 246 := by
  have hc : ((-95071/125000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60615082967/1250000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-95071/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c247 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-7663/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3562883/5000000) (δ := 12451/1000000000) (ψ := 495907/500000) 246 216
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t247 : ((-4876106469/80000000000 : ℚ) : ℝ) ≤ stT246 247 := by
  have hc : ((-38317/40000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4876106469/80000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-38317/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c248 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((-140853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -116023/250000) (δ := 12451/1000000000) (ψ := 495907/500000) 246 216
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t248 : ((-44728835439/2500000000000 : ℚ) : ℝ) ≤ stT246 248 := by
  have hc : ((-70439/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44728835439/2500000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-70439/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c249 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((80943/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1083049/5000000) (δ := 193/15625000) (ψ := 495907/500000) 246 216
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t249 : ((51291560957/1250000000000 : ℚ) : ℝ) ≤ stT246 249 := by
  have hc : ((323747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51291560957/1250000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((323747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_c250 :
    |Real.cos (((246 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((496431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 298883/10000000) (δ := 12451/1000000000) (ψ := 495907/500000) 246 216
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st246_t250 : ((31395445673/500000000000 : ℚ) : ℝ) ≤ stT246 250 := by
  have hc : ((248203/250000 : ℚ) : ℝ)
      ≤ Real.cos (((246 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((495907/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st246_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31395445673/500000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((248203/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st246_p1 : ((273561/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT246 (i+1) := by
  rw [Finset.sum_range_one]
  exact st246_t1

theorem st246_p2 : ((12487974134373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT246 (i+1))
      = (∑ i ∈ Finset.range 1, stT246 (i+1)) + stT246 2 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 1
    simpa using h
  have hprev := st246_p1
  have hstep := st246_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p3 : ((16030375568497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT246 (i+1))
      = (∑ i ∈ Finset.range 2, stT246 (i+1)) + stT246 3 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 2
    simpa using h
  have hprev := st246_p2
  have hstep := st246_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p4 : ((19706955568497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT246 (i+1))
      = (∑ i ∈ Finset.range 3, stT246 (i+1)) + stT246 4 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 3
    simpa using h
  have hprev := st246_p3
  have hstep := st246_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p5 : ((5612206502283/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT246 (i+1))
      = (∑ i ∈ Finset.range 4, stT246 (i+1)) + stT246 5 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 4
    simpa using h
  have hprev := st246_p4
  have hstep := st246_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p6 : ((3315938912609/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT246 (i+1))
      = (∑ i ∈ Finset.range 5, stT246 (i+1)) + stT246 6 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 5
    simpa using h
  have hprev := st246_p5
  have hstep := st246_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p7 : ((472592224847/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT246 (i+1))
      = (∑ i ∈ Finset.range 6, stT246 (i+1)) + stT246 7 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 6
    simpa using h
  have hprev := st246_p6
  have hstep := st246_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p8 : ((15048636038191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT246 (i+1))
      = (∑ i ∈ Finset.range 7, stT246 (i+1)) + stT246 8 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 7
    simpa using h
  have hprev := st246_p7
  have hstep := st246_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p9 : ((16175175925537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT246 (i+1))
      = (∑ i ∈ Finset.range 8, stT246 (i+1)) + stT246 9 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 8
    simpa using h
  have hprev := st246_p8
  have hstep := st246_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p10 : ((17754802857131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT246 (i+1))
      = (∑ i ∈ Finset.range 9, stT246 (i+1)) + stT246 10 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 9
    simpa using h
  have hprev := st246_p9
  have hstep := st246_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p11 : ((17517217904159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT246 (i+1))
      = (∑ i ∈ Finset.range 10, stT246 (i+1)) + stT246 11 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 10
    simpa using h
  have hprev := st246_p10
  have hstep := st246_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p12 : ((4623808677301/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT246 (i+1))
      = (∑ i ∈ Finset.range 11, stT246 (i+1)) + stT246 12 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 11
    simpa using h
  have hprev := st246_p11
  have hstep := st246_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p13 : ((9180845318027/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT246 (i+1))
      = (∑ i ∈ Finset.range 12, stT246 (i+1)) + stT246 13 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 12
    simpa using h
  have hprev := st246_p12
  have hstep := st246_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p14 : ((4757151888251/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT246 (i+1))
      = (∑ i ∈ Finset.range 13, stT246 (i+1)) + stT246 14 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 13
    simpa using h
  have hprev := st246_p13
  have hstep := st246_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p15 : ((9950332481523/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT246 (i+1))
      = (∑ i ∈ Finset.range 14, stT246 (i+1)) + stT246 15 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 14
    simpa using h
  have hprev := st246_p14
  have hstep := st246_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p16 : ((3782712413641/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT246 (i+1))
      = (∑ i ∈ Finset.range 15, stT246 (i+1)) + stT246 16 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 15
    simpa using h
  have hprev := st246_p15
  have hstep := st246_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p17 : ((19053733092869/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT246 (i+1))
      = (∑ i ∈ Finset.range 16, stT246 (i+1)) + stT246 17 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 16
    simpa using h
  have hprev := st246_p16
  have hstep := st246_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p18 : ((20231256500651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT246 (i+1))
      = (∑ i ∈ Finset.range 17, stT246 (i+1)) + stT246 18 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 17
    simpa using h
  have hprev := st246_p17
  have hstep := st246_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p19 : ((2631451578937/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT246 (i+1))
      = (∑ i ∈ Finset.range 18, stT246 (i+1)) + stT246 19 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 18
    simpa using h
  have hprev := st246_p18
  have hstep := st246_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p20 : ((21809681829769/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT246 (i+1))
      = (∑ i ∈ Finset.range 19, stT246 (i+1)) + stT246 20 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 19
    simpa using h
  have hprev := st246_p19
  have hstep := st246_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p21 : ((11431789439513/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT246 (i+1))
      = (∑ i ∈ Finset.range 20, stT246 (i+1)) + stT246 21 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 20
    simpa using h
  have hprev := st246_p20
  have hstep := st246_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p22 : ((23558385036277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT246 (i+1))
      = (∑ i ∈ Finset.range 21, stT246 (i+1)) + stT246 22 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 21
    simpa using h
  have hprev := st246_p21
  have hstep := st246_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p23 : ((45456175190569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT246 (i+1))
      = (∑ i ∈ Finset.range 22, stT246 (i+1)) + stT246 23 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 22
    simpa using h
  have hprev := st246_p22
  have hstep := st246_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p24 : ((45204298175221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT246 (i+1))
      = (∑ i ∈ Finset.range 23, stT246 (i+1)) + stT246 24 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 23
    simpa using h
  have hprev := st246_p23
  have hstep := st246_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p25 : ((46554386175221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT246 (i+1))
      = (∑ i ∈ Finset.range 24, stT246 (i+1)) + stT246 25 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 24
    simpa using h
  have hprev := st246_p24
  have hstep := st246_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p26 : ((44942556156471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT246 (i+1))
      = (∑ i ∈ Finset.range 25, stT246 (i+1)) + stT246 26 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 25
    simpa using h
  have hprev := st246_p25
  have hstep := st246_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p27 : ((46354715766471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT246 (i+1))
      = (∑ i ∈ Finset.range 26, stT246 (i+1)) + stT246 27 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 26
    simpa using h
  have hprev := st246_p26
  have hstep := st246_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p28 : ((11428597232301/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT246 (i+1))
      = (∑ i ∈ Finset.range 27, stT246 (i+1)) + stT246 28 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 27
    simpa using h
  have hprev := st246_p27
  have hstep := st246_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p29 : ((4491210866609/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT246 (i+1))
      = (∑ i ∈ Finset.range 28, stT246 (i+1)) + stT246 29 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 28
    simpa using h
  have hprev := st246_p28
  have hstep := st246_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p30 : ((11684090878229/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT246 (i+1))
      = (∑ i ∈ Finset.range 29, stT246 (i+1)) + stT246 30 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 29
    simpa using h
  have hprev := st246_p29
  have hstep := st246_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p31 : ((11572361950997/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT246 (i+1))
      = (∑ i ∈ Finset.range 30, stT246 (i+1)) + stT246 31 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 30
    simpa using h
  have hprev := st246_p30
  have hstep := st246_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p32 : ((4455955697973/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT246 (i+1))
      = (∑ i ∈ Finset.range 31, stT246 (i+1)) + stT246 32 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 31
    simpa using h
  have hprev := st246_p31
  have hstep := st246_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p33 : ((44426347501359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT246 (i+1))
      = (∑ i ∈ Finset.range 32, stT246 (i+1)) + stT246 33 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 32
    simpa using h
  have hprev := st246_p32
  have hstep := st246_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p34 : ((22927230907727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT246 (i+1))
      = (∑ i ∈ Finset.range 33, stT246 (i+1)) + stT246 34 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 33
    simpa using h
  have hprev := st246_p33
  have hstep := st246_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p35 : ((23743708832507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT246 (i+1))
      = (∑ i ∈ Finset.range 34, stT246 (i+1)) + stT246 35 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 34
    simpa using h
  have hprev := st246_p34
  have hstep := st246_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p36 : ((6064124865181/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT246 (i+1))
      = (∑ i ∈ Finset.range 35, stT246 (i+1)) + stT246 36 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 35
    simpa using h
  have hprev := st246_p35
  have hstep := st246_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p37 : ((48849064796817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT246 (i+1))
      = (∑ i ∈ Finset.range 36, stT246 (i+1)) + stT246 37 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 36
    simpa using h
  have hprev := st246_p36
  have hstep := st246_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p38 : ((12183366844533/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT246 (i+1))
      = (∑ i ∈ Finset.range 37, stT246 (i+1)) + stT246 38 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 37
    simpa using h
  have hprev := st246_p37
  have hstep := st246_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p39 : ((24224886525019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT246 (i+1))
      = (∑ i ∈ Finset.range 38, stT246 (i+1)) + stT246 39 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 38
    simpa using h
  have hprev := st246_p38
  have hstep := st246_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p40 : ((12063906248057/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT246 (i+1))
      = (∑ i ∈ Finset.range 39, stT246 (i+1)) + stT246 40 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 39
    simpa using h
  have hprev := st246_p39
  have hstep := st246_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p41 : ((12097327419857/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT246 (i+1))
      = (∑ i ∈ Finset.range 40, stT246 (i+1)) + stT246 41 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 40
    simpa using h
  have hprev := st246_p40
  have hstep := st246_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p42 : ((3065485702349/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT246 (i+1))
      = (∑ i ∈ Finset.range 41, stT246 (i+1)) + stT246 42 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 41
    simpa using h
  have hprev := st246_p41
  have hstep := st246_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p43 : ((50275251488889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT246 (i+1))
      = (∑ i ∈ Finset.range 42, stT246 (i+1)) + stT246 43 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 42
    simpa using h
  have hprev := st246_p42
  have hstep := st246_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p44 : ((51782691407077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT246 (i+1))
      = (∑ i ∈ Finset.range 43, stT246 (i+1)) + stT246 44 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 43
    simpa using h
  have hprev := st246_p43
  have hstep := st246_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p45 : ((26437964830507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT246 (i+1))
      = (∑ i ∈ Finset.range 44, stT246 (i+1)) + stT246 45 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 44
    simpa using h
  have hprev := st246_p44
  have hstep := st246_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p46 : ((26398843307437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT246 (i+1))
      = (∑ i ∈ Finset.range 45, stT246 (i+1)) + stT246 46 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 45
    simpa using h
  have hprev := st246_p45
  have hstep := st246_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p47 : ((25767748174387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT246 (i+1))
      = (∑ i ∈ Finset.range 46, stT246 (i+1)) + stT246 47 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 46
    simpa using h
  have hprev := st246_p46
  have hstep := st246_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p48 : ((1006544954851/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT246 (i+1))
      = (∑ i ∈ Finset.range 47, stT246 (i+1)) + stT246 48 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 47
    simpa using h
  have hprev := st246_p47
  have hstep := st246_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p49 : ((50637531935179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT246 (i+1))
      = (∑ i ∈ Finset.range 48, stT246 (i+1)) + stT246 49 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 48
    simpa using h
  have hprev := st246_p48
  have hstep := st246_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p50 : ((6506328286587/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT246 (i+1))
      = (∑ i ∈ Finset.range 49, stT246 (i+1)) + stT246 50 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 49
    simpa using h
  have hprev := st246_p49
  have hstep := st246_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p51 : ((6540674004357/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT246 (i+1))
      = (∑ i ∈ Finset.range 50, stT246 (i+1)) + stT246 51 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 50
    simpa using h
  have hprev := st246_p50
  have hstep := st246_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p52 : ((50985902895687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT246 (i+1))
      = (∑ i ∈ Finset.range 51, stT246 (i+1)) + stT246 52 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 51
    simpa using h
  have hprev := st246_p51
  have hstep := st246_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p53 : ((50665349957891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT246 (i+1))
      = (∑ i ∈ Finset.range 52, stT246 (i+1)) + stT246 53 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 52
    simpa using h
  have hprev := st246_p52
  have hstep := st246_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p54 : ((52016101394783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT246 (i+1))
      = (∑ i ∈ Finset.range 53, stT246 (i+1)) + stT246 54 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 53
    simpa using h
  have hprev := st246_p53
  have hstep := st246_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p55 : ((51912099302783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT246 (i+1))
      = (∑ i ∈ Finset.range 54, stT246 (i+1)) + stT246 55 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 54
    simpa using h
  have hprev := st246_p54
  have hstep := st246_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p56 : ((50659976971169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT246 (i+1))
      = (∑ i ∈ Finset.range 55, stT246 (i+1)) + stT246 56 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 55
    simpa using h
  have hprev := st246_p55
  have hstep := st246_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p57 : ((51528578566129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT246 (i+1))
      = (∑ i ∈ Finset.range 56, stT246 (i+1)) + stT246 57 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 56
    simpa using h
  have hprev := st246_p56
  have hstep := st246_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p58 : ((52065737291761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT246 (i+1))
      = (∑ i ∈ Finset.range 57, stT246 (i+1)) + stT246 58 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 57
    simpa using h
  have hprev := st246_p57
  have hstep := st246_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p59 : ((50768554926001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT246 (i+1))
      = (∑ i ∈ Finset.range 58, stT246 (i+1)) + stT246 59 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 58
    simpa using h
  have hprev := st246_p58
  have hstep := st246_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p60 : ((51563585179033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT246 (i+1))
      = (∑ i ∈ Finset.range 59, stT246 (i+1)) + stT246 60 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 59
    simpa using h
  have hprev := st246_p59
  have hstep := st246_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p61 : ((51894058402777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT246 (i+1))
      = (∑ i ∈ Finset.range 60, stT246 (i+1)) + stT246 61 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 60
    simpa using h
  have hprev := st246_p60
  have hstep := st246_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p62 : ((50751084542821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT246 (i+1))
      = (∑ i ∈ Finset.range 61, stT246 (i+1)) + stT246 62 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 61
    simpa using h
  have hprev := st246_p61
  have hstep := st246_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p63 : ((10387476186627/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT246 (i+1))
      = (∑ i ∈ Finset.range 62, stT246 (i+1)) + stT246 63 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 62
    simpa using h
  have hprev := st246_p62
  have hstep := st246_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p64 : ((2567176835403/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT246 (i+1))
      = (∑ i ∈ Finset.range 63, stT246 (i+1)) + stT246 64 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 63
    simpa using h
  have hprev := st246_p63
  have hstep := st246_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p65 : ((12781132735599/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT246 (i+1))
      = (∑ i ∈ Finset.range 64, stT246 (i+1)) + stT246 65 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 64
    simpa using h
  have hprev := st246_p64
  have hstep := st246_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p66 : ((5200029055689/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT246 (i+1))
      = (∑ i ∈ Finset.range 65, stT246 (i+1)) + stT246 66 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 65
    simpa using h
  have hprev := st246_p65
  have hstep := st246_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p67 : ((5080835604709/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT246 (i+1))
      = (∑ i ∈ Finset.range 66, stT246 (i+1)) + stT246 67 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 66
    simpa using h
  have hprev := st246_p66
  have hstep := st246_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p68 : ((1299330908593/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT246 (i+1))
      = (∑ i ∈ Finset.range 67, stT246 (i+1)) + stT246 68 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 67
    simpa using h
  have hprev := st246_p67
  have hstep := st246_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p69 : ((12769269722171/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT246 (i+1))
      = (∑ i ∈ Finset.range 68, stT246 (i+1)) + stT246 69 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 68
    simpa using h
  have hprev := st246_p68
  have hstep := st246_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p70 : ((2579388914949/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT246 (i+1))
      = (∑ i ∈ Finset.range 69, stT246 (i+1)) + stT246 70 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 69
    simpa using h
  have hprev := st246_p69
  have hstep := st246_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p71 : ((6434581894149/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT246 (i+1))
      = (∑ i ∈ Finset.range 70, stT246 (i+1)) + stT246 71 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 70
    simpa using h
  have hprev := st246_p70
  have hstep := st246_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p72 : ((6404540592071/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT246 (i+1))
      = (∑ i ∈ Finset.range 71, stT246 (i+1)) + stT246 72 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 71
    simpa using h
  have hprev := st246_p71
  have hstep := st246_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p73 : ((3234536771689/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT246 (i+1))
      = (∑ i ∈ Finset.range 72, stT246 (i+1)) + stT246 73 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 72
    simpa using h
  have hprev := st246_p72
  have hstep := st246_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p74 : ((51037721953397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT246 (i+1))
      = (∑ i ∈ Finset.range 73, stT246 (i+1)) + stT246 74 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 73
    simpa using h
  have hprev := st246_p73
  have hstep := st246_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p75 : ((51884081257697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT246 (i+1))
      = (∑ i ∈ Finset.range 74, stT246 (i+1)) + stT246 75 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 74
    simpa using h
  have hprev := st246_p74
  have hstep := st246_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p76 : ((12739511382019/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT246 (i+1))
      = (∑ i ∈ Finset.range 75, stT246 (i+1)) + stT246 76 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 75
    simpa using h
  have hprev := st246_p75
  have hstep := st246_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p77 : ((25962615285393/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT246 (i+1))
      = (∑ i ∈ Finset.range 76, stT246 (i+1)) + stT246 77 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 76
    simpa using h
  have hprev := st246_p76
  have hstep := st246_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p78 : ((25472560837881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT246 (i+1))
      = (∑ i ∈ Finset.range 77, stT246 (i+1)) + stT246 78 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 77
    simpa using h
  have hprev := st246_p77
  have hstep := st246_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p79 : ((51914470757961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT246 (i+1))
      = (∑ i ∈ Finset.range 78, stT246 (i+1)) + stT246 79 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 78
    simpa using h
  have hprev := st246_p78
  have hstep := st246_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p80 : ((50978937919917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT246 (i+1))
      = (∑ i ∈ Finset.range 79, stT246 (i+1)) + stT246 80 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 79
    simpa using h
  have hprev := st246_p79
  have hstep := st246_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p81 : ((51853100054723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT246 (i+1))
      = (∑ i ∈ Finset.range 80, stT246 (i+1)) + stT246 81 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 80
    simpa using h
  have hprev := st246_p80
  have hstep := st246_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p82 : ((51074478868287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT246 (i+1))
      = (∑ i ∈ Finset.range 81, stT246 (i+1)) + stT246 82 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 81
    simpa using h
  have hprev := st246_p81
  have hstep := st246_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p83 : ((51714623682687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT246 (i+1))
      = (∑ i ∈ Finset.range 82, stT246 (i+1)) + stT246 83 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 82
    simpa using h
  have hprev := st246_p82
  have hstep := st246_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p84 : ((51262439980717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT246 (i+1))
      = (∑ i ∈ Finset.range 83, stT246 (i+1)) + stT246 84 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 83
    simpa using h
  have hprev := st246_p83
  have hstep := st246_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p85 : ((51474626112869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT246 (i+1))
      = (∑ i ∈ Finset.range 84, stT246 (i+1)) + stT246 85 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 84
    simpa using h
  have hprev := st246_p84
  have hstep := st246_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p86 : ((12886807197863/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT246 (i+1))
      = (∑ i ∈ Finset.range 85, stT246 (i+1)) + stT246 86 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 85
    simpa using h
  have hprev := st246_p85
  have hstep := st246_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p87 : ((25582221855079/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT246 (i+1))
      = (∑ i ∈ Finset.range 86, stT246 (i+1)) + stT246 87 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 86
    simpa using h
  have hprev := st246_p86
  have hstep := st246_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p88 : ((10369437117113/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT246 (i+1))
      = (∑ i ∈ Finset.range 87, stT246 (i+1)) + stT246 88 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 87
    simpa using h
  have hprev := st246_p87
  have hstep := st246_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p89 : ((50923949587523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT246 (i+1))
      = (∑ i ∈ Finset.range 88, stT246 (i+1)) + stT246 89 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 88
    simpa using h
  have hprev := st246_p88
  have hstep := st246_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p90 : ((51970314039071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT246 (i+1))
      = (∑ i ∈ Finset.range 89, stT246 (i+1)) + stT246 90 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 89
    simpa using h
  have hprev := st246_p89
  have hstep := st246_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p91 : ((50969600212371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT246 (i+1))
      = (∑ i ∈ Finset.range 90, stT246 (i+1)) + stT246 91 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 90
    simpa using h
  have hprev := st246_p90
  have hstep := st246_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p92 : ((51728373688251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT246 (i+1))
      = (∑ i ∈ Finset.range 91, stT246 (i+1)) + stT246 92 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 91
    simpa using h
  have hprev := st246_p91
  have hstep := st246_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p93 : ((51389309049387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT246 (i+1))
      = (∑ i ∈ Finset.range 92, stT246 (i+1)) + stT246 93 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 92
    simpa using h
  have hprev := st246_p92
  have hstep := st246_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p94 : ((51207146515701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT246 (i+1))
      = (∑ i ∈ Finset.range 93, stT246 (i+1)) + stT246 94 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 93
    simpa using h
  have hprev := st246_p93
  have hstep := st246_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p95 : ((51880433292443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT246 (i+1))
      = (∑ i ∈ Finset.range 94, stT246 (i+1)) + stT246 95 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 94
    simpa using h
  have hprev := st246_p94
  have hstep := st246_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p96 : ((12725540229899/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT246 (i+1))
      = (∑ i ∈ Finset.range 95, stT246 (i+1)) + stT246 96 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 95
    simpa using h
  have hprev := st246_p95
  have hstep := st246_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p97 : ((5187117566627/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT246 (i+1))
      = (∑ i ∈ Finset.range 96, stT246 (i+1)) + stT246 97 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 96
    simpa using h
  have hprev := st246_p96
  have hstep := st246_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p98 : ((51260428071093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT246 (i+1))
      = (∑ i ∈ Finset.range 97, stT246 (i+1)) + stT246 98 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 97
    simpa using h
  have hprev := st246_p97
  have hstep := st246_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p99 : ((51265513558313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT246 (i+1))
      = (∑ i ∈ Finset.range 98, stT246 (i+1)) + stT246 99 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 98
    simpa using h
  have hprev := st246_p98
  have hstep := st246_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p100 : ((10376364188401/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT246 (i+1))
      = (∑ i ∈ Finset.range 99, stT246 (i+1)) + stT246 100 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 99
    simpa using h
  have hprev := st246_p99
  have hstep := st246_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p101 : ((50909197167993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT246 (i+1))
      = (∑ i ∈ Finset.range 100, stT246 (i+1)) + stT246 101 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 100
    simpa using h
  have hprev := st246_p100
  have hstep := st246_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p102 : ((51775682728869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT246 (i+1))
      = (∑ i ∈ Finset.range 101, stT246 (i+1)) + stT246 102 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 101
    simpa using h
  have hprev := st246_p101
  have hstep := st246_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p103 : ((51461783194779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT246 (i+1))
      = (∑ i ∈ Finset.range 102, stT246 (i+1)) + stT246 103 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 102
    simpa using h
  have hprev := st246_p102
  have hstep := st246_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p104 : ((1595110591331/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT246 (i+1))
      = (∑ i ∈ Finset.range 103, stT246 (i+1)) + stT246 104 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 103
    simpa using h
  have hprev := st246_p103
  have hstep := st246_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p105 : ((12990660141673/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT246 (i+1))
      = (∑ i ∈ Finset.range 104, stT246 (i+1)) + stT246 105 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 104
    simpa using h
  have hprev := st246_p104
  have hstep := st246_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p106 : ((12773840939179/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT246 (i+1))
      = (∑ i ∈ Finset.range 105, stT246 (i+1)) + stT246 106 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 105
    simpa using h
  have hprev := st246_p105
  have hstep := st246_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p107 : ((12838751944531/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT246 (i+1))
      = (∑ i ∈ Finset.range 106, stT246 (i+1)) + stT246 107 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 106
    simpa using h
  have hprev := st246_p106
  have hstep := st246_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p108 : ((6485411100203/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT246 (i+1))
      = (∑ i ∈ Finset.range 107, stT246 (i+1)) + stT246 108 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 107
    simpa using h
  have hprev := st246_p107
  have hstep := st246_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p109 : ((795808877103/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT246 (i+1))
      = (∑ i ∈ Finset.range 108, stT246 (i+1)) + stT246 109 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 108
    simpa using h
  have hprev := st246_p108
  have hstep := st246_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p110 : ((25804860307729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT246 (i+1))
      = (∑ i ∈ Finset.range 109, stT246 (i+1)) + stT246 110 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 109
    simpa using h
  have hprev := st246_p109
  have hstep := st246_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p111 : ((5172731737113/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT246 (i+1))
      = (∑ i ∈ Finset.range 110, stT246 (i+1)) + stT246 111 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 110
    simpa using h
  have hprev := st246_p110
  have hstep := st246_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p112 : ((25451582089909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT246 (i+1))
      = (∑ i ∈ Finset.range 111, stT246 (i+1)) + stT246 112 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 111
    simpa using h
  have hprev := st246_p111
  have hstep := st246_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p113 : ((25876376435269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT246 (i+1))
      = (∑ i ∈ Finset.range 112, stT246 (i+1)) + stT246 113 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 112
    simpa using h
  have hprev := st246_p112
  have hstep := st246_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p114 : ((6451254369909/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT246 (i+1))
      = (∑ i ∈ Finset.range 113, stT246 (i+1)) + stT246 114 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 113
    simpa using h
  have hprev := st246_p113
  have hstep := st246_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p115 : ((50915494977717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT246 (i+1))
      = (∑ i ∈ Finset.range 114, stT246 (i+1)) + stT246 115 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 114
    simpa using h
  have hprev := st246_p114
  have hstep := st246_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p116 : ((51807481870917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT246 (i+1))
      = (∑ i ∈ Finset.range 115, stT246 (i+1)) + stT246 116 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 115
    simpa using h
  have hprev := st246_p115
  have hstep := st246_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p117 : ((51570020091063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT246 (i+1))
      = (∑ i ∈ Finset.range 116, stT246 (i+1)) + stT246 117 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 116
    simpa using h
  have hprev := st246_p116
  have hstep := st246_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p118 : ((50917177759463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT246 (i+1))
      = (∑ i ∈ Finset.range 117, stT246 (i+1)) + stT246 118 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 117
    simpa using h
  have hprev := st246_p117
  have hstep := st246_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p119 : ((51797340760673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT246 (i+1))
      = (∑ i ∈ Finset.range 118, stT246 (i+1)) + stT246 119 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 118
    simpa using h
  have hprev := st246_p118
  have hstep := st246_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p120 : ((12902931446843/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT246 (i+1))
      = (∑ i ∈ Finset.range 119, stT246 (i+1)) + stT246 120 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 119
    simpa using h
  have hprev := st246_p119
  have hstep := st246_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p121 : ((10180436597829/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT246 (i+1))
      = (∑ i ∈ Finset.range 120, stT246 (i+1)) + stT246 121 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 120
    simpa using h
  have hprev := st246_p120
  have hstep := st246_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p122 : ((25860345904103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT246 (i+1))
      = (∑ i ∈ Finset.range 121, stT246 (i+1)) + stT246 122 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 121
    simpa using h
  have hprev := st246_p121
  have hstep := st246_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p123 : ((25862170882159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT246 (i+1))
      = (∑ i ∈ Finset.range 122, stT246 (i+1)) + stT246 123 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 122
    simpa using h
  have hprev := st246_p122
  have hstep := st246_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p124 : ((50903229878841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT246 (i+1))
      = (∑ i ∈ Finset.range 123, stT246 (i+1)) + stT246 124 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 123
    simpa using h
  have hprev := st246_p123
  have hstep := st246_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p125 : ((25779223424913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT246 (i+1))
      = (∑ i ∈ Finset.range 124, stT246 (i+1)) + stT246 125 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 124
    simpa using h
  have hprev := st246_p124
  have hstep := st246_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p126 : ((25935813426553/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT246 (i+1))
      = (∑ i ∈ Finset.range 125, stT246 (i+1)) + stT246 126 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 125
    simpa using h
  have hprev := st246_p125
  have hstep := st246_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p127 : ((25492159772549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT246 (i+1))
      = (∑ i ∈ Finset.range 126, stT246 (i+1)) + stT246 127 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 126
    simpa using h
  have hprev := st246_p126
  have hstep := st246_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p128 : ((51306548815461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT246 (i+1))
      = (∑ i ∈ Finset.range 127, stT246 (i+1)) + stT246 128 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 127
    simpa using h
  have hprev := st246_p127
  have hstep := st246_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p129 : ((51970262841211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT246 (i+1))
      = (∑ i ∈ Finset.range 128, stT246 (i+1)) + stT246 129 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 128
    simpa using h
  have hprev := st246_p128
  have hstep := st246_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p130 : ((2048453607211/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT246 (i+1))
      = (∑ i ∈ Finset.range 129, stT246 (i+1)) + stT246 130 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 129
    simpa using h
  have hprev := st246_p129
  have hstep := st246_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p131 : ((10205685308741/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT246 (i+1))
      = (∑ i ∈ Finset.range 130, stT246 (i+1)) + stT246 131 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 130
    simpa using h
  have hprev := st246_p130
  have hstep := st246_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p132 : ((51895320806273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT246 (i+1))
      = (∑ i ∈ Finset.range 131, stT246 (i+1)) + stT246 132 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 131
    simpa using h
  have hprev := st246_p131
  have hstep := st246_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p133 : ((51577770383403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT246 (i+1))
      = (∑ i ∈ Finset.range 132, stT246 (i+1)) + stT246 133 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 132
    simpa using h
  have hprev := st246_p132
  have hstep := st246_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p134 : ((10177668144567/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT246 (i+1))
      = (∑ i ∈ Finset.range 133, stT246 (i+1)) + stT246 134 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 133
    simpa using h
  have hprev := st246_p133
  have hstep := st246_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p135 : ((2062605579991/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT246 (i+1))
      = (∑ i ∈ Finset.range 134, stT246 (i+1)) + stT246 135 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 134
    simpa using h
  have hprev := st246_p134
  have hstep := st246_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p136 : ((51915605912587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT246 (i+1))
      = (∑ i ∈ Finset.range 135, stT246 (i+1)) + stT246 136 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 135
    simpa using h
  have hprev := st246_p135
  have hstep := st246_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p137 : ((51076527251059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT246 (i+1))
      = (∑ i ∈ Finset.range 136, stT246 (i+1)) + stT246 137 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 136
    simpa using h
  have hprev := st246_p136
  have hstep := st246_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p138 : ((51100840824931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT246 (i+1))
      = (∑ i ∈ Finset.range 137, stT246 (i+1)) + stT246 138 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 137
    simpa using h
  have hprev := st246_p137
  have hstep := st246_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p139 : ((51925868203403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT246 (i+1))
      = (∑ i ∈ Finset.range 138, stT246 (i+1)) + stT246 139 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 138
    simpa using h
  have hprev := st246_p138
  have hstep := st246_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p140 : ((51576067000453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT246 (i+1))
      = (∑ i ∈ Finset.range 139, stT246 (i+1)) + stT246 140 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 139
    simpa using h
  have hprev := st246_p139
  have hstep := st246_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p141 : ((10176838731249/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT246 (i+1))
      = (∑ i ∈ Finset.range 140, stT246 (i+1)) + stT246 141 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 140
    simpa using h
  have hprev := st246_p140
  have hstep := st246_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p142 : ((10294206585909/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT246 (i+1))
      = (∑ i ∈ Finset.range 141, stT246 (i+1)) + stT246 142 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 141
    simpa using h
  have hprev := st246_p141
  have hstep := st246_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p143 : ((51970911637401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT246 (i+1))
      = (∑ i ∈ Finset.range 142, stT246 (i+1)) + stT246 143 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 142
    simpa using h
  have hprev := st246_p142
  have hstep := st246_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p144 : ((51238473551451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT246 (i+1))
      = (∑ i ∈ Finset.range 143, stT246 (i+1)) + stT246 144 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 143
    simpa using h
  have hprev := st246_p143
  have hstep := st246_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p145 : ((50941497860721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT246 (i+1))
      = (∑ i ∈ Finset.range 144, stT246 (i+1)) + stT246 145 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 144
    simpa using h
  have hprev := st246_p144
  have hstep := st246_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p146 : ((51744203536691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT246 (i+1))
      = (∑ i ∈ Finset.range 145, stT246 (i+1)) + stT246 146 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 145
    simpa using h
  have hprev := st246_p145
  have hstep := st246_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p147 : ((51857081274293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT246 (i+1))
      = (∑ i ∈ Finset.range 146, stT246 (i+1)) + stT246 147 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 146
    simpa using h
  have hprev := st246_p146
  have hstep := st246_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p148 : ((25517856728239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT246 (i+1))
      = (∑ i ∈ Finset.range 147, stT246 (i+1)) + stT246 148 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 147
    simpa using h
  have hprev := st246_p147
  have hstep := st246_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p149 : ((51072905724647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT246 (i+1))
      = (∑ i ∈ Finset.range 148, stT246 (i+1)) + stT246 149 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 148
    simpa using h
  have hprev := st246_p148
  have hstep := st246_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p150 : ((51883475596679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT246 (i+1))
      = (∑ i ∈ Finset.range 149, stT246 (i+1)) + stT246 150 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 149
    simpa using h
  have hprev := st246_p149
  have hstep := st246_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p151 : ((12933652904069/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT246 (i+1))
      = (∑ i ∈ Finset.range 150, stT246 (i+1)) + stT246 151 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 150
    simpa using h
  have hprev := st246_p150
  have hstep := st246_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p152 : ((6368264359249/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT246 (i+1))
      = (∑ i ∈ Finset.range 151, stT246 (i+1)) + stT246 152 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 151
    simpa using h
  have hprev := st246_p151
  have hstep := st246_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p153 : ((2558444150707/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT246 (i+1))
      = (∑ i ∈ Finset.range 152, stT246 (i+1)) + stT246 153 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 152
    simpa using h
  have hprev := st246_p152
  have hstep := st246_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p154 : ((12983999942959/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT246 (i+1))
      = (∑ i ∈ Finset.range 153, stT246 (i+1)) + stT246 154 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 153
    simpa using h
  have hprev := st246_p153
  have hstep := st246_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p155 : ((12918451166809/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT246 (i+1))
      = (∑ i ∈ Finset.range 154, stT246 (i+1)) + stT246 155 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 154
    simpa using h
  have hprev := st246_p154
  have hstep := st246_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p156 : ((1591248234987/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT246 (i+1))
      = (∑ i ∈ Finset.range 155, stT246 (i+1)) + stT246 156 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 155
    simpa using h
  have hprev := st246_p155
  have hstep := st246_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p157 : ((1023792830393/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT246 (i+1))
      = (∑ i ∈ Finset.range 156, stT246 (i+1)) + stT246 157 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 156
    simpa using h
  have hprev := st246_p156
  have hstep := st246_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p158 : ((51940703812197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT246 (i+1))
      = (∑ i ∈ Finset.range 157, stT246 (i+1)) + stT246 158 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 157
    simpa using h
  have hprev := st246_p157
  have hstep := st246_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p159 : ((51693346928137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT246 (i+1))
      = (∑ i ∈ Finset.range 158, stT246 (i+1)) + stT246 159 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 158
    simpa using h
  have hprev := st246_p158
  have hstep := st246_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p160 : ((50935448023957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT246 (i+1))
      = (∑ i ∈ Finset.range 159, stT246 (i+1)) + stT246 160 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 159
    simpa using h
  have hprev := st246_p159
  have hstep := st246_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p161 : ((51130829950277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT246 (i+1))
      = (∑ i ∈ Finset.range 160, stT246 (i+1)) + stT246 161 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 160
    simpa using h
  have hprev := st246_p160
  have hstep := st246_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p162 : ((51900330065313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT246 (i+1))
      = (∑ i ∈ Finset.range 161, stT246 (i+1)) + stT246 162 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 161
    simpa using h
  have hprev := st246_p161
  have hstep := st246_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p163 : ((51786282564147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT246 (i+1))
      = (∑ i ∈ Finset.range 162, stT246 (i+1)) + stT246 163 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 162
    simpa using h
  have hprev := st246_p162
  have hstep := st246_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p164 : ((255039315751/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT246 (i+1))
      = (∑ i ∈ Finset.range 163, stT246 (i+1)) + stT246 164 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 163
    simpa using h
  have hprev := st246_p163
  have hstep := st246_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p165 : ((797052015989/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT246 (i+1))
      = (∑ i ∈ Finset.range 164, stT246 (i+1)) + stT246 165 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 164
    simpa using h
  have hprev := st246_p164
  have hstep := st246_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p166 : ((25892482536723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT246 (i+1))
      = (∑ i ∈ Finset.range 165, stT246 (i+1)) + stT246 166 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 165
    simpa using h
  have hprev := st246_p165
  have hstep := st246_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p167 : ((6489783945207/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT246 (i+1))
      = (∑ i ∈ Finset.range 166, stT246 (i+1)) + stT246 167 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 166
    simpa using h
  have hprev := st246_p166
  have hstep := st246_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p168 : ((6396971993141/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT246 (i+1))
      = (∑ i ∈ Finset.range 167, stT246 (i+1)) + stT246 168 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 167
    simpa using h
  have hprev := st246_p167
  have hstep := st246_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p169 : ((50886010473583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT246 (i+1))
      = (∑ i ∈ Finset.range 168, stT246 (i+1)) + stT246 169 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 168
    simpa using h
  have hprev := st246_p168
  have hstep := st246_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p170 : ((51556961318279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT246 (i+1))
      = (∑ i ∈ Finset.range 169, stT246 (i+1)) + stT246 170 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 169
    simpa using h
  have hprev := st246_p169
  have hstep := st246_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p171 : ((2600484474797/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT246 (i+1))
      = (∑ i ∈ Finset.range 170, stT246 (i+1)) + stT246 171 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 170
    simpa using h
  have hprev := st246_p170
  have hstep := st246_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p172 : ((6432782396447/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT246 (i+1))
      = (∑ i ∈ Finset.range 171, stT246 (i+1)) + stT246 172 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 171
    simpa using h
  have hprev := st246_p171
  have hstep := st246_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p173 : ((25429886405867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT246 (i+1))
      = (∑ i ∈ Finset.range 172, stT246 (i+1)) + stT246 173 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 172
    simpa using h
  have hprev := st246_p172
  have hstep := st246_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p174 : ((25612637300237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT246 (i+1))
      = (∑ i ∈ Finset.range 173, stT246 (i+1)) + stT246 174 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 173
    simpa using h
  have hprev := st246_p173
  have hstep := st246_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p175 : ((25968680522129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT246 (i+1))
      = (∑ i ∈ Finset.range 174, stT246 (i+1)) + stT246 175 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 174
    simpa using h
  have hprev := st246_p174
  have hstep := st246_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p176 : ((10361512512359/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT246 (i+1))
      = (∑ i ∈ Finset.range 175, stT246 (i+1)) + stT246 176 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 175
    simpa using h
  have hprev := st246_p175
  have hstep := st246_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p177 : ((51055883992621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT246 (i+1))
      = (∑ i ∈ Finset.range 176, stT246 (i+1)) + stT246 177 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 176
    simpa using h
  have hprev := st246_p176
  have hstep := st246_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p178 : ((50915113638169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT246 (i+1))
      = (∑ i ∈ Finset.range 177, stT246 (i+1)) + stT246 178 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 177
    simpa using h
  have hprev := st246_p177
  have hstep := st246_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p179 : ((403193538533/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT246 (i+1))
      = (∑ i ∈ Finset.range 178, stT246 (i+1)) + stT246 179 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 178
    simpa using h
  have hprev := st246_p178
  have hstep := st246_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p180 : ((26009177969847/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT246 (i+1))
      = (∑ i ∈ Finset.range 179, stT246 (i+1)) + stT246 180 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 179
    simpa using h
  have hprev := st246_p179
  have hstep := st246_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p181 : ((51495021999159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT246 (i+1))
      = (∑ i ∈ Finset.range 180, stT246 (i+1)) + stT246 181 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 180
    simpa using h
  have hprev := st246_p180
  have hstep := st246_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p182 : ((50869176470409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT246 (i+1))
      = (∑ i ∈ Finset.range 181, stT246 (i+1)) + stT246 182 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 181
    simpa using h
  have hprev := st246_p181
  have hstep := st246_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p183 : ((51117591687459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT246 (i+1))
      = (∑ i ∈ Finset.range 182, stT246 (i+1)) + stT246 183 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 182
    simpa using h
  have hprev := st246_p182
  have hstep := st246_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p184 : ((51850097294039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT246 (i+1))
      = (∑ i ∈ Finset.range 183, stT246 (i+1)) + stT246 184 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 183
    simpa using h
  have hprev := st246_p183
  have hstep := st246_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p185 : ((51941631437039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT246 (i+1))
      = (∑ i ∈ Finset.range 184, stT246 (i+1)) + stT246 185 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 184
    simpa using h
  have hprev := st246_p184
  have hstep := st246_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p186 : ((51257855138183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT246 (i+1))
      = (∑ i ∈ Finset.range 185, stT246 (i+1)) + stT246 186 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 185
    simpa using h
  have hprev := st246_p185
  have hstep := st246_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p187 : ((25416081421529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT246 (i+1))
      = (∑ i ∈ Finset.range 186, stT246 (i+1)) + stT246 187 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 186
    simpa using h
  have hprev := st246_p186
  have hstep := st246_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p188 : ((5129676994537/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT246 (i+1))
      = (∑ i ∈ Finset.range 187, stT246 (i+1)) + stT246 188 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 187
    simpa using h
  have hprev := st246_p187
  have hstep := st246_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p189 : ((5195942405737/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT246 (i+1))
      = (∑ i ∈ Finset.range 188, stT246 (i+1)) + stT246 189 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 188
    simpa using h
  have hprev := st246_p188
  have hstep := st246_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p190 : ((5184931115831/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT246 (i+1))
      = (∑ i ∈ Finset.range 189, stT246 (i+1)) + stT246 190 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 189
    simpa using h
  have hprev := st246_p189
  have hstep := st246_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p191 : ((5113153922981/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT246 (i+1))
      = (∑ i ∈ Finset.range 190, stT246 (i+1)) + stT246 191 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 190
    simpa using h
  have hprev := st246_p190
  have hstep := st246_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p192 : ((25420812806601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT246 (i+1))
      = (∑ i ∈ Finset.range 191, stT246 (i+1)) + stT246 192 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 191
    simpa using h
  have hprev := st246_p191
  have hstep := st246_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p193 : ((51389244309457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT246 (i+1))
      = (∑ i ∈ Finset.range 192, stT246 (i+1)) + stT246 193 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 192
    simpa using h
  have hprev := st246_p192
  have hstep := st246_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p194 : ((10399108521893/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT246 (i+1))
      = (∑ i ∈ Finset.range 193, stT246 (i+1)) + stT246 194 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 193
    simpa using h
  have hprev := st246_p193
  have hstep := st246_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p195 : ((414496213463/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT246 (i+1))
      = (∑ i ∈ Finset.range 194, stT246 (i+1)) + stT246 195 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 194
    simpa using h
  have hprev := st246_p194
  have hstep := st246_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p196 : ((51098722111839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT246 (i+1))
      = (∑ i ∈ Finset.range 195, stT246 (i+1)) + stT246 196 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 195
    simpa using h
  have hprev := st246_p195
  have hstep := st246_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p197 : ((50839549386053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT246 (i+1))
      = (∑ i ∈ Finset.range 196, stT246 (i+1)) + stT246 197 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 196
    simpa using h
  have hprev := st246_p196
  have hstep := st246_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p198 : ((51384216057019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT246 (i+1))
      = (∑ i ∈ Finset.range 197, stT246 (i+1)) + stT246 198 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 197
    simpa using h
  have hprev := st246_p197
  have hstep := st246_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p199 : ((2599576464811/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT246 (i+1))
      = (∑ i ∈ Finset.range 198, stT246 (i+1)) + stT246 199 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 198
    simpa using h
  have hprev := st246_p198
  have hstep := st246_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p200 : ((2073926958343/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT246 (i+1))
      = (∑ i ∈ Finset.range 199, stT246 (i+1)) + stT246 200 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 199
    simpa using h
  have hprev := st246_p199
  have hstep := st246_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p201 : ((51149669109429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT246 (i+1))
      = (∑ i ∈ Finset.range 200, stT246 (i+1)) + stT246 201 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 200
    simpa using h
  have hprev := st246_p200
  have hstep := st246_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p202 : ((50818676205887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT246 (i+1))
      = (∑ i ∈ Finset.range 201, stT246 (i+1)) + stT246 202 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 201
    simpa using h
  have hprev := st246_p201
  have hstep := st246_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p203 : ((51284124413531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT246 (i+1))
      = (∑ i ∈ Finset.range 202, stT246 (i+1)) + stT246 203 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 202
    simpa using h
  have hprev := st246_p202
  have hstep := st246_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p204 : ((51938568376151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT246 (i+1))
      = (∑ i ∈ Finset.range 203, stT246 (i+1)) + stT246 204 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 203
    simpa using h
  have hprev := st246_p203
  have hstep := st246_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p205 : ((51941820266231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT246 (i+1))
      = (∑ i ∈ Finset.range 204, stT246 (i+1)) + stT246 205 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 204
    simpa using h
  have hprev := st246_p204
  have hstep := st246_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p206 : ((51294345360031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT246 (i+1))
      = (∑ i ∈ Finset.range 205, stT246 (i+1)) + stT246 206 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 205
    simpa using h
  have hprev := st246_p205
  have hstep := st246_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p207 : ((25408258969427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT246 (i+1))
      = (∑ i ∈ Finset.range 206, stT246 (i+1)) + stT246 207 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 206
    simpa using h
  have hprev := st246_p206
  have hstep := st246_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p208 : ((12776006470651/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT246 (i+1))
      = (∑ i ∈ Finset.range 207, stT246 (i+1)) + stT246 208 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 207
    simpa using h
  have hprev := st246_p207
  have hstep := st246_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p209 : ((25897619886691/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT246 (i+1))
      = (∑ i ∈ Finset.range 208, stT246 (i+1)) + stT246 209 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 208
    simpa using h
  have hprev := st246_p208
  have hstep := st246_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p210 : ((6504777665099/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT246 (i+1))
      = (∑ i ∈ Finset.range 209, stT246 (i+1)) + stT246 210 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 209
    simpa using h
  have hprev := st246_p209
  have hstep := st246_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p211 : ((51540153265727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT246 (i+1))
      = (∑ i ∈ Finset.range 210, stT246 (i+1)) + stT246 211 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 210
    simpa using h
  have hprev := st246_p210
  have hstep := st246_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p212 : ((2545391064923/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT246 (i+1))
      = (∑ i ∈ Finset.range 211, stT246 (i+1)) + stT246 212 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 211
    simpa using h
  have hprev := st246_p211
  have hstep := st246_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p213 : ((50899521604103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT246 (i+1))
      = (∑ i ∈ Finset.range 212, stT246 (i+1)) + stT246 213 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 212
    simpa using h
  have hprev := st246_p212
  have hstep := st246_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p214 : ((6440083237431/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT246 (i+1))
      = (∑ i ∈ Finset.range 213, stT246 (i+1)) + stT246 214 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 213
    simpa using h
  have hprev := st246_p213
  have hstep := st246_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p215 : ((26017524822019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT246 (i+1))
      = (∑ i ∈ Finset.range 214, stT246 (i+1)) + stT246 215 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 214
    simpa using h
  have hprev := st246_p214
  have hstep := st246_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p216 : ((1620075742507/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT246 (i+1))
      = (∑ i ∈ Finset.range 215, stT246 (i+1)) + stT246 216 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 215
    simpa using h
  have hprev := st246_p215
  have hstep := st246_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p217 : ((51170923184279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT246 (i+1))
      = (∑ i ∈ Finset.range 216, stT246 (i+1)) + stT246 217 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 216
    simpa using h
  have hprev := st246_p216
  have hstep := st246_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p218 : ((50795574669509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT246 (i+1))
      = (∑ i ∈ Finset.range 217, stT246 (i+1)) + stT246 218 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 217
    simpa using h
  have hprev := st246_p217
  have hstep := st246_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p219 : ((6392763856001/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT246 (i+1))
      = (∑ i ∈ Finset.range 218, stT246 (i+1)) + stT246 219 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 218
    simpa using h
  have hprev := st246_p218
  have hstep := st246_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p220 : ((6324907229/1220703125 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT246 (i+1))
      = (∑ i ∈ Finset.range 219, stT246 (i+1)) + stT246 220 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 219
    simpa using h
  have hprev := st246_p219
  have hstep := st246_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p221 : ((813355740163/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT246 (i+1))
      = (∑ i ∈ Finset.range 220, stT246 (i+1)) + stT246 221 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 220
    simpa using h
  have hprev := st246_p220
  have hstep := st246_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p222 : ((1032004847999/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT246 (i+1))
      = (∑ i ∈ Finset.range 221, stT246 (i+1)) + stT246 222 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 221
    simpa using h
  have hprev := st246_p221
  have hstep := st246_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p223 : ((1019128121363/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT246 (i+1))
      = (∑ i ∈ Finset.range 222, stT246 (i+1)) + stT246 223 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 222
    simpa using h
  have hprev := st246_p222
  have hstep := st246_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p224 : ((25414642212209/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT246 (i+1))
      = (∑ i ∈ Finset.range 223, stT246 (i+1)) + stT246 224 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 223
    simpa using h
  have hprev := st246_p223
  have hstep := st246_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p225 : ((12838322475103/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT246 (i+1))
      = (∑ i ∈ Finset.range 224, stT246 (i+1)) + stT246 225 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 224
    simpa using h
  have hprev := st246_p224
  have hstep := st246_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p226 : ((811865693383/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT246 (i+1))
      = (∑ i ∈ Finset.range 225, stT246 (i+1)) + stT246 226 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 225
    simpa using h
  have hprev := st246_p225
  have hstep := st246_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p227 : ((51999292137643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT246 (i+1))
      = (∑ i ∈ Finset.range 226, stT246 (i+1)) + stT246 227 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 226
    simpa using h
  have hprev := st246_p226
  have hstep := st246_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p228 : ((25717271645563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT246 (i+1))
      = (∑ i ∈ Finset.range 227, stT246 (i+1)) + stT246 228 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 227
    simpa using h
  have hprev := st246_p227
  have hstep := st246_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p229 : ((203453314817/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT246 (i+1))
      = (∑ i ∈ Finset.range 228, stT246 (i+1)) + stT246 229 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 228
    simpa using h
  have hprev := st246_p228
  have hstep := st246_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p230 : ((5088177683789/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT246 (i+1))
      = (∑ i ∈ Finset.range 229, stT246 (i+1)) + stT246 230 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 229
    simpa using h
  have hprev := st246_p229
  have hstep := st246_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p231 : ((12866674806149/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT246 (i+1))
      = (∑ i ∈ Finset.range 230, stT246 (i+1)) + stT246 231 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 230
    simpa using h
  have hprev := st246_p230
  have hstep := st246_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p232 : ((3250828841129/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT246 (i+1))
      = (∑ i ∈ Finset.range 231, stT246 (i+1)) + stT246 232 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 231
    simpa using h
  have hprev := st246_p231
  have hstep := st246_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p233 : ((1623892080817/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT246 (i+1))
      = (∑ i ∈ Finset.range 232, stT246 (i+1)) + stT246 233 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 232
    simpa using h
  have hprev := st246_p232
  have hstep := st246_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p234 : ((5137386128729/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT246 (i+1))
      = (∑ i ∈ Finset.range 233, stT246 (i+1)) + stT246 234 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 233
    simpa using h
  have hprev := st246_p233
  have hstep := st246_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p235 : ((50837720562467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT246 (i+1))
      = (∑ i ∈ Finset.range 234, stT246 (i+1)) + stT246 235 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 234
    simpa using h
  have hprev := st246_p234
  have hstep := st246_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p236 : ((50889682818211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT246 (i+1))
      = (∑ i ∈ Finset.range 235, stT246 (i+1)) + stT246 236 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 235
    simpa using h
  have hprev := st246_p235
  have hstep := st246_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p237 : ((51474362473387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT246 (i+1))
      = (∑ i ∈ Finset.range 236, stT246 (i+1)) + stT246 237 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 236
    simpa using h
  have hprev := st246_p236
  have hstep := st246_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p238 : ((5201470514239/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT246 (i+1))
      = (∑ i ∈ Finset.range 237, stT246 (i+1)) + stT246 238 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 237
    simpa using h
  have hprev := st246_p237
  have hstep := st246_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p239 : ((51985078902943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT246 (i+1))
      = (∑ i ∈ Finset.range 238, stT246 (i+1)) + stT246 239 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 238
    simpa using h
  have hprev := st246_p238
  have hstep := st246_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p240 : ((51417914021737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT246 (i+1))
      = (∑ i ∈ Finset.range 239, stT246 (i+1)) + stT246 240 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 239
    simpa using h
  have hprev := st246_p239
  have hstep := st246_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p241 : ((50860473437077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT246 (i+1))
      = (∑ i ∈ Finset.range 240, stT246 (i+1)) + stT246 241 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 240
    simpa using h
  have hprev := st246_p240
  have hstep := st246_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p242 : ((25421488191701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT246 (i+1))
      = (∑ i ∈ Finset.range 241, stT246 (i+1)) + stT246 242 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 241
    simpa using h
  have hprev := st246_p241
  have hstep := st246_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p243 : ((25689143802701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT246 (i+1))
      = (∑ i ∈ Finset.range 242, stT246 (i+1)) + stT246 243 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 242
    simpa using h
  have hprev := st246_p242
  have hstep := st246_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p244 : ((1039220583509/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT246 (i+1))
      = (∑ i ∈ Finset.range 243, stT246 (i+1)) + stT246 244 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 243
    simpa using h
  have hprev := st246_p243
  have hstep := st246_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p245 : ((26024420382511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT246 (i+1))
      = (∑ i ∈ Finset.range 244, stT246 (i+1)) + stT246 245 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 244
    simpa using h
  have hprev := st246_p244
  have hstep := st246_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p246 : ((25781960050643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT246 (i+1))
      = (∑ i ∈ Finset.range 245, stT246 (i+1)) + stT246 246 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 245
    simpa using h
  have hprev := st246_p245
  have hstep := st246_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p247 : ((50954406792661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT246 (i+1))
      = (∑ i ∈ Finset.range 246, stT246 (i+1)) + stT246 247 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 246
    simpa using h
  have hprev := st246_p246
  have hstep := st246_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p248 : ((10155098290181/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT246 (i+1))
      = (∑ i ∈ Finset.range 247, stT246 (i+1)) + stT246 248 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 247
    simpa using h
  have hprev := st246_p247
  have hstep := st246_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p249 : ((51185823938561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT246 (i+1))
      = (∑ i ∈ Finset.range 248, stT246 (i+1)) + stT246 249 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 248
    simpa using h
  have hprev := st246_p248
  have hstep := st246_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_p250 : ((51813732852021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT246 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT246 (i+1))
      = (∑ i ∈ Finset.range 249, stT246 (i+1)) + stT246 250 := by
    have h := Finset.sum_range_succ (fun i => stT246 (i+1)) 249
    simpa using h
  have hprev := st246_p249
  have hstep := st246_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st246_s250 :
    |Real.sin (((246 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((495907/500000 : ℚ) : ℝ))
      - ((119269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 298883/10000000) (δ := 12451/1000000000) (ψ := 495907/500000) 246 216
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 246`** (evaluated boundary). -/
theorem station_246_sign : 0 < hardyG ((((246:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 246 250 (by norm_num) (by norm_num)
    ((495907/500000 : ℚ) : ℝ)
  have hchain := st246_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT246 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((246 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((495907/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st246_c250
  have hsinb := abs_le.mp st246_s250
  have hbdy_lo : ((-235976685901/30258125000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((246 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((495907/500000 : ℚ) : ℝ))) / 2
          - ((((246:ℕ)):ℝ))
            * Real.sin (((246 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((495907/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((246:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((246:ℝ) * Real.log (250:ℝ) - ((495907/500000 : ℚ) : ℝ))) / 2
        - ((246:ℝ)) * Real.sin ((246:ℝ) * Real.log (250:ℝ) - ((495907/500000 : ℚ) : ℝ))
        ≥ ((-2984893/100000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((246:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-2984893/100000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-2984893/100000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-2984893/100000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((246:ℕ)):ℝ))+1) * (((((246:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((311897336597/234375000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((51813732852021/10000000000000 : ℚ) : ℝ) + ((-235976685901/30258125000000 : ℚ) : ℝ)
      - ((311897336597/234375000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((495907/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((246:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((495907/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((246:ℕ)):ℝ)))).re
      - Real.sin ((495907/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((246:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((246:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((246:ℕ)):ℝ))
      = (((((246:ℕ)):ℝ)) * (Real.log ((((246:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((246:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_246
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
  have hθwin : |(((495907/500000 : ℚ) : ℝ) + ((52:ℤ)) * (2*Real.pi)) - theta ((((246:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((246:ℕ)):ℝ)))
    (φ := ((495907/500000 : ℚ) : ℝ) + ((52:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((495907/500000 : ℚ)) : ℝ) 52).1,
    (cos_sin_shift (((495907/500000 : ℚ)) : ℝ) 52).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_246_sign
end AxiomAudit
