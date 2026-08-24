import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 139` (rung-144.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT139 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((139 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((820771/1000000 : ℚ) : ℝ))

theorem st139_c1 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((681657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -256491/1250000) (δ := 201/1000000000) (ψ := 820771/1000000) 139 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t1 : ((681607/1000000 : ℚ) : ℝ) ≤ stT139 1 := by
  have hc : ((681607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((681607/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((681607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c2 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((143883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1598629/5000000) (δ := 3497/500000000) (ψ := 820771/1000000) 139 15
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t2 : ((508614778243/2500000000000 : ℚ) : ℝ) ≤ stT139 2 := by
  have hc : ((71929/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((508614778243/2500000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((71929/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c3 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((115647/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2724711/10000000) (δ := 3487/500000000) (ψ := 820771/1000000) 139 24
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t3 : ((667616017019/2500000000000 : ℚ) : ℝ) ≤ stT139 3 := by
  have hc : ((231269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((667616017019/2500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((231269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c4 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-972049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3630751/5000000) (δ := 439/62500000) (ψ := 820771/1000000) 139 31
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t4 : ((-4860495972099/10000000000000 : ℚ) : ℝ) ≤ stT139 4 := by
  have hc : ((-972099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4860495972099/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-972099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c5 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-986911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3724523/5000000) (δ := 7053/1000000000) (ψ := 820771/1000000) 139 35
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t5 : ((-551727977337/1250000000000 : ℚ) : ℝ) ≤ stT139 5 := by
  have hc : ((-986961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-551727977337/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-986961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c6 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-19977/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7734049/10000000) (δ := 7089/1000000000) (ψ := 820771/1000000) 139 40
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t6 : ((-40779922687/100000000000 : ℚ) : ℝ) ≤ stT139 6 := by
  have hc : ((-9989/10000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40779922687/100000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-9989/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c7 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((869687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1290571/10000000) (δ := 6993/1000000000) (ψ := 820771/1000000) 139 43
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t7 : ((821729567307/2500000000000 : ℚ) : ℝ) ≤ stT139 7 := by
  have hc : ((869637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((821729567307/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((869637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c8 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((693169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2012299/10000000) (δ := 879/125000000) (ψ := 820771/1000000) 139 46
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t8 : ((2450545097427/10000000000000 : ℚ) : ℝ) ≤ stT139 8 := by
  have hc : ((693119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2450545097427/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((693119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c9 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-99007/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7501367/10000000) (δ := 3523/500000000) (ψ := 820771/1000000) 139 48
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t9 : ((-41255008251/125000000000 : ℚ) : ℝ) ≤ stT139 9 := by
  have hc : ((-24753/25000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41255008251/125000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-24753/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c10 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((1121/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3009749/10000000) (δ := 1767/250000000) (ψ := 820771/1000000) 139 51
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t10 : ((113421389159/1000000000000 : ℚ) : ℝ) ≤ stT139 10 := by
  have hc : ((35867/100000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113421389159/1000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((35867/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c11 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((216687/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1305381/10000000) (δ := 3541/500000000) (ψ := 820771/1000000) 139 53
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t11 : ((1306596203437/5000000000000 : ℚ) : ℝ) ≤ stT139 11 := by
  have hc : ((433349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1306596203437/5000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((433349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c12 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((545393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1242423/5000000) (δ := 887/125000000) (ψ := 820771/1000000) 139 55
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t12 : ((1574269450593/10000000000000 : ℚ) : ℝ) ≤ stT139 12 := by
  have hc : ((545343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1574269450593/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((545343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c13 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-190043/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1217187/2000000) (δ := 1773/250000000) (ψ := 820771/1000000) 139 57
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t13 : ((-1054238238611/5000000000000 : ℚ) : ℝ) ≤ stT139 13 := by
  have hc : ((-380111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1054238238611/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-380111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c14 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-791/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 494829/1250000) (δ := 1397/200000000) (ψ := 820771/1000000) 139 58
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t14 : ((-16979110389/5000000000000 : ℚ) : ℝ) ≤ stT139 14 := by
  have hc : ((-6353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16979110389/5000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-6353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c15 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((35391/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1741131/5000000) (δ := 7071/1000000000) (ψ := 820771/1000000) 139 60
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t15 : ((22838329357/500000000000 : ℚ) : ℝ) ≤ stT139 15 := by
  have hc : ((35381/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22838329357/500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((35381/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c16 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((272543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 404613/1250000) (δ := 7039/1000000000) (ψ := 820771/1000000) 139 61
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t16 : ((272493/4000000 : ℚ) : ℝ) ≤ stT139 16 := by
  have hc : ((272493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272493/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((272493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c17 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-239069/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3555987/5000000) (δ := 3527/500000000) (ψ := 820771/1000000) 139 63
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t17 : ((-1159715979191/5000000000000 : ℚ) : ℝ) ≤ stT139 17 := by
  have hc : ((-478163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1159715979191/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-478163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c18 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((378189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1478697/5000000) (δ := 3571/500000000) (ψ := 820771/1000000) 139 64
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t18 : ((445640971029/5000000000000 : ℚ) : ℝ) ≤ stT139 18 := by
  have hc : ((378139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((445640971029/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((378139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c19 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((99879/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24599/2000000) (δ := 1407/200000000) (ψ := 820771/1000000) 139 65
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t19 : ((114563318109/500000000000 : ℚ) : ℝ) ≤ stT139 19 := by
  have hc : ((49937/50000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114563318109/500000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((49937/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c20 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((624909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1119727/5000000) (δ := 283/40000000) (ψ := 820771/1000000) 139 66
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t20 : ((1397226589553/10000000000000 : ℚ) : ℝ) ≤ stT139 20 := by
  have hc : ((624859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1397226589553/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((624859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c21 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((175449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 697217/2000000) (δ := 6983/1000000000) (ψ := 820771/1000000) 139 67
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t21 : ((191375919511/5000000000000 : ℚ) : ℝ) ≤ stT139 21 := by
  have hc : ((175399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191375919511/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((175399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c22 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-1683/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1971911/5000000) (δ := 709/100000000) (ψ := 820771/1000000) 139 68
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t22 : ((-903704891/625000000000 : ℚ) : ℝ) ≤ stT139 22 := by
  have hc : ((-3391/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-903704891/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-3391/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c23 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((48749/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3682859/10000000) (δ := 6997/1000000000) (ψ := 820771/1000000) 139 69
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t23 : ((3174892383/156250000000 : ℚ) : ℝ) ≤ stT139 23 := by
  have hc : ((12181/125000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3174892383/156250000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((12181/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c24 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((448471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2764357/10000000) (δ := 111/15625000) (ψ := 820771/1000000) 139 70
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t24 : ((915335330461/10000000000000 : ℚ) : ℝ) ≤ stT139 24 := by
  have hc : ((448421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((915335330461/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((448421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c25 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((175821/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 621019/5000000) (δ := 1773/250000000) (ψ := 820771/1000000) 139 71
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t25 : ((175811/1000000 : ℚ) : ℝ) ≤ stT139 25 := by
  have hc : ((175811/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175811/1000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((175811/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c26 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((944511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -209183/2500000) (δ := 1417/200000000) (ψ := 820771/1000000) 139 72
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t26 : ((1852240079221/10000000000000 : ℚ) : ℝ) ≤ stT139 26 := by
  have hc : ((944461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1852240079221/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((944461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c27 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((197513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3429941/10000000) (δ := 7077/1000000000) (ψ := 820771/1000000) 139 73
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t27 : ((760035087/20000000000 : ℚ) : ℝ) ≤ stT139 27 := by
  have hc : ((197463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((760035087/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((197463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c28 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-171383/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -203129/312500) (δ := 7033/1000000000) (ψ := 820771/1000000) 139 74
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t28 : ((-323902433439/2000000000000 : ℚ) : ℝ) ≤ stT139 28 := by
  have hc : ((-171393/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-323902433439/2000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-171393/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c29 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-649437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5694099/10000000) (δ := 7133/1000000000) (ψ := 820771/1000000) 139 74
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t29 : ((-603033741299/5000000000000 : ℚ) : ℝ) ≤ stT139 29 := by
  have hc : ((-649487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-603033741299/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-649487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c30 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((190117/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1766907/10000000) (δ := 357/50000000) (ψ := 820771/1000000) 139 75
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t30 : ((694163159869/5000000000000 : ℚ) : ℝ) ≤ stT139 30 := by
  have hc : ((380209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((694163159869/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((380209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c31 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((65567/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1273283/5000000) (δ := 7147/1000000000) (ψ := 820771/1000000) 139 76
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t31 : ((471002326879/5000000000000 : ℚ) : ℝ) ≤ stT139 31 := by
  have hc : ((262243/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((471002326879/5000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((262243/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c32 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-968203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7221857/10000000) (δ := 7149/1000000000) (ψ := 820771/1000000) 139 77
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t32 : ((-1711645701051/10000000000000 : ℚ) : ℝ) ≤ stT139 32 := by
  have hc : ((-968253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1711645701051/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-968253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c33 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((181279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1735637/5000000) (δ := 7149/1000000000) (ψ := 820771/1000000) 139 77
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t33 : ((39434886713/1250000000000 : ℚ) : ℝ) ≤ stT139 33 := by
  have hc : ((181229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39434886713/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((181229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c34 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((367507/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1862771/10000000) (δ := 3531/500000000) (ψ := 820771/1000000) 139 78
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t34 : ((63022611777/500000000000 : ℚ) : ℝ) ≤ stT139 34 := by
  have hc : ((183741/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63022611777/500000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((183741/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c35 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-197971/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3748789/5000000) (δ := 7069/1000000000) (ψ := 820771/1000000) 139 79
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t35 : ((-334649066129/2000000000000 : ℚ) : ℝ) ≤ stT139 35 := by
  have hc : ((-197981/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-334649066129/2000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-197981/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c36 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((76053/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2291809/10000000) (δ := 3567/500000000) (ψ := 820771/1000000) 139 79
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t36 : ((253489065271/2500000000000 : ℚ) : ℝ) ≤ stT139 36 := by
  have hc : ((304187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((253489065271/2500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((304187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c37 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((3199/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3895001/10000000) (δ := 1769/250000000) (ψ := 820771/1000000) 139 80
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t37 : ((10477141897/5000000000000 : ℚ) : ℝ) ≤ stT139 37 := by
  have hc : ((6373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10477141897/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((6373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c38 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-546419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2686099/5000000) (δ := 7027/1000000000) (ψ := 820771/1000000) 139 80
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t38 : ((-177298041767/2000000000000 : ℚ) : ℝ) ≤ stT139 38 := by
  have hc : ((-546469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177298041767/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-546469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c39 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((865969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1309279/10000000) (δ := 351/50000000) (ψ := 820771/1000000) 139 81
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t39 : ((1386579642239/10000000000000 : ℚ) : ℝ) ≤ stT139 39 := by
  have hc : ((865919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1386579642239/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((865919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c40 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-494671/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7488657/10000000) (δ := 7083/1000000000) (ψ := 820771/1000000) 139 81
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t40 : ((-97772892343/625000000000 : ℚ) : ℝ) ≤ stT139 40 := by
  have hc : ((-61837/62500 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97772892343/625000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-61837/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c41 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((989571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 90343/2500000) (δ := 699/100000000) (ψ := 820771/1000000) 139 82
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t41 : ((1545371557977/10000000000000 : ℚ) : ℝ) ≤ stT139 41 := by
  have hc : ((989521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1545371557977/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((989521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c42 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-187701/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -278907/400000) (δ := 7097/1000000000) (ψ := 820771/1000000) 139 83
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t42 : ((-144822227587/1000000000000 : ℚ) : ℝ) ≤ stT139 42 := by
  have hc : ((-187711/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144822227587/1000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-187711/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c43 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((886223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1204173/10000000) (δ := 3553/500000000) (ψ := 820771/1000000) 139 83
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t43 : ((270280106481/2000000000000 : ℚ) : ℝ) ≤ stT139 43 := by
  have hc : ((886173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270280106481/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((886173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c44 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-429977/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6514939/10000000) (δ := 3549/500000000) (ψ := 820771/1000000) 139 84
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t44 : ((-324126262557/2500000000000 : ℚ) : ℝ) ≤ stT139 44 := by
  have hc : ((-215001/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324126262557/2500000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-215001/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c45 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((434469/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1294359/10000000) (δ := 3549/500000000) (ψ := 820771/1000000) 139 84
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t45 : ((161907612421/1250000000000 : ℚ) : ℝ) ≤ stT139 45 := by
  have hc : ((108611/125000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161907612421/1250000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((108611/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c46 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-908457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -52937/78125) (δ := 1753/250000000) (ψ := 820771/1000000) 139 85
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t46 : ((-66976044547/500000000000 : ℚ) : ℝ) ≤ stT139 46 := by
  have hc : ((-908507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66976044547/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-908507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c47 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((961331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 697503/10000000) (δ := 6991/1000000000) (ψ := 820771/1000000) 139 85
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t47 : ((1402171569369/10000000000000 : ℚ) : ℝ) ≤ stT139 47 := by
  have hc : ((961281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1402171569369/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((961281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c48 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-997963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1923601/2500000) (δ := 1771/250000000) (ψ := 820771/1000000) 139 86
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t48 : ((-90031750743/625000000000 : ℚ) : ℝ) ≤ stT139 48 := by
  have hc : ((-998013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90031750743/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-998013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c49 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((977677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33077/625000) (δ := 1771/250000000) (ψ := 820771/1000000) 139 86
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t49 : ((1396609581017/10000000000000 : ℚ) : ℝ) ≤ stT139 49 := by
  have hc : ((977627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1396609581017/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((977627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c50 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-855077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6491241/10000000) (δ := 1771/250000000) (ψ := 820771/1000000) 139 86
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t50 : ((-604666287589/5000000000000 : ℚ) : ℝ) ≤ stT139 50 := by
  have hc : ((-855127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-604666287589/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-855127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c51 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((14863/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1167659/5000000) (δ := 3563/500000000) (ψ := 820771/1000000) 139 87
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t51 : ((2081061129/25000000000 : ℚ) : ℝ) ≤ stT139 51 := by
  have hc : ((59447/100000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2081061129/25000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((59447/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c52 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-96487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4412471/10000000) (δ := 7077/1000000000) (ψ := 820771/1000000) 139 87
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t52 : ((-522805127/19531250000 : ℚ) : ℝ) ≤ stT139 52 := by
  have hc : ((-3016/15625 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-522805127/19531250000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-3016/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c53 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-147617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2338121/5000000) (δ := 7133/1000000000) (ψ := 820771/1000000) 139 88
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t53 : ((-50700484263/1250000000000 : ℚ) : ℝ) ≤ stT139 53 := by
  have hc : ((-73821/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50700484263/1250000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-73821/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c54 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((746703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 909631/5000000) (δ := 707/100000000) (ψ := 820771/1000000) 139 88
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t54 : ((1016065562031/10000000000000 : ℚ) : ℝ) ≤ stT139 54 := by
  have hc : ((746653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1016065562031/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((746653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c55 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-24767/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7512389/10000000) (δ := 7063/1000000000) (ψ := 820771/1000000) 139 89
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t55 : ((-333975083/2500000000 : ℚ) : ℝ) ≤ stT139 55 := by
  have hc : ((-99073/100000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333975083/2500000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-99073/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c56 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((438699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15637/125000) (δ := 6963/1000000000) (ψ := 820771/1000000) 139 89
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t56 : ((146550674561/1250000000000 : ℚ) : ℝ) ≤ stT139 56 := by
  have hc : ((219337/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146550674561/1250000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((219337/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c57 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-379323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4899651/10000000) (δ := 6963/1000000000) (ψ := 820771/1000000) 139 89
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t57 : ((-502492057809/10000000000000 : ℚ) : ℝ) ≤ stT139 57 := by
  have hc : ((-379373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-502492057809/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-379373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c58 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-164417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2382331/5000000) (δ := 1411/200000000) (ψ := 820771/1000000) 139 90
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t58 : ((-21592303473/500000000000 : ℚ) : ℝ) ≤ stT139 58 := by
  have hc : ((-82221/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21592303473/500000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-82221/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c59 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((222863/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 587821/5000000) (δ := 1411/200000000) (ψ := 820771/1000000) 139 90
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t59 : ((580253229189/5000000000000 : ℚ) : ℝ) ≤ stT139 59 := by
  have hc : ((445701/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((580253229189/5000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((445701/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c60 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-944361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 701611/1000000) (δ := 1787/250000000) (ψ := 820771/1000000) 139 90
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t60 : ((-243845975789/2000000000000 : ℚ) : ℝ) ≤ stT139 60 := by
  have hc : ((-944411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243845975789/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-944411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c61 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((381693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1473961/5000000) (δ := 1391/200000000) (ψ := 820771/1000000) 139 91
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t61 : ((30540217789/625000000000 : ℚ) : ℝ) ≤ stT139 61 := by
  have hc : ((381643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30540217789/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((381643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c62 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((47041/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1351301/5000000) (δ := 1411/200000000) (ψ := 820771/1000000) 139 91
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t62 : ((14933941759/250000000000 : ℚ) : ℝ) ≤ stT139 62 := by
  have hc : ((11759/25000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14933941759/250000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((11759/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c63 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-986663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7445223/10000000) (δ := 7141/1000000000) (ψ := 820771/1000000) 139 92
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t63 : ((-621570973933/5000000000000 : ℚ) : ℝ) ≤ stT139 63 := by
  have hc : ((-986713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-621570973933/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-986713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c64 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((352251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -123293/625000) (δ := 3531/500000000) (ψ := 820771/1000000) 139 92
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t64 : ((176113/2000000 : ℚ) : ℝ) ≤ stT139 64 := by
  have hc : ((176113/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176113/2000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((176113/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c65 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((1271/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3415021/10000000) (δ := 7041/1000000000) (ψ := 820771/1000000) 139 92
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t65 : ((25217494857/1000000000000 : ℚ) : ℝ) ≤ stT139 65 := by
  have hc : ((20331/100000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25217494857/1000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((20331/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c66 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-470267/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3493743/5000000) (δ := 3517/500000000) (ψ := 820771/1000000) 139 93
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t66 : ((-28944473859/250000000000 : ℚ) : ℝ) ≤ stT139 66 := by
  have hc : ((-117573/125000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28944473859/250000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-117573/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c67 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((761789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -220227/1250000) (δ := 3567/500000000) (ψ := 820771/1000000) 139 93
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t67 : ((465305982933/5000000000000 : ℚ) : ℝ) ≤ stT139 67 := by
  have hc : ((761739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((465305982933/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((761739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c68 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((214543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 52913/156250) (δ := 7069/1000000000) (ψ := 820771/1000000) 139 93
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t68 : ((130055471127/5000000000000 : ℚ) : ℝ) ≤ stT139 68 := by
  have hc : ((214493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130055471127/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((214493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c69 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-97081/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7248449/10000000) (δ := 7127/1000000000) (ψ := 820771/1000000) 139 94
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t69 : ((-58438927437/500000000000 : ℚ) : ℝ) ≤ stT139 69 := by
  have hc : ((-48543/50000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58438927437/500000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-48543/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c70 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((622119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17987/80000) (δ := 1769/250000000) (ψ := 820771/1000000) 139 94
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t70 : ((185878571683/2500000000000 : ℚ) : ℝ) ≤ stT139 70 := by
  have hc : ((622069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185878571683/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((622069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c71 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((478097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2680773/10000000) (δ := 7027/1000000000) (ψ := 820771/1000000) 139 94
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t71 : ((567337096707/10000000000000 : ℚ) : ℝ) ≤ stT139 71 := by
  have hc : ((478047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((567337096707/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((478047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c72 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-496087/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1885253/2500000) (δ := 7127/1000000000) (ψ := 820771/1000000) 139 94
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t72 : ((-2283882599/19531250000 : ℚ) : ℝ) ≤ stT139 72 := by
  have hc : ((-31007/31250 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2283882599/19531250000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-31007/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c73 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((219483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3373779/10000000) (δ := 873/125000000) (ψ := 820771/1000000) 139 95
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t73 : ((256826796963/10000000000000 : ℚ) : ℝ) ≤ stT139 73 := by
  have hc : ((219433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((256826796963/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((219433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c74 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((856851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1354167/10000000) (δ := 873/125000000) (ψ := 820771/1000000) 139 95
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t74 : ((249002649819/2500000000000 : ℚ) : ℝ) ≤ stT139 74 := by
  have hc : ((856801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249002649819/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((856801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c75 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-92803/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3009347/5000000) (δ := 7019/1000000000) (ψ := 820771/1000000) 139 95
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t75 : ((-428667735137/5000000000000 : ℚ) : ℝ) ≤ stT139 75 := by
  have hc : ((-371237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-428667735137/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-371237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c76 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-3579/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2543281/5000000) (δ := 6991/1000000000) (ψ := 820771/1000000) 139 96
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t76 : ((-20529272863/400000000000 : ℚ) : ℝ) ≤ stT139 76 := by
  have hc : ((-17897/40000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20529272863/400000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-17897/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c77 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((488209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -544007/10000000) (δ := 7091/1000000000) (ψ := 820771/1000000) 139 96
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t77 : ((13908423183/125000000000 : ℚ) : ℝ) ≤ stT139 77 := by
  have hc : ((61023/62500 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13908423183/125000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((61023/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c78 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-5173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 984981/2500000) (δ := 1753/250000000) (ψ := 820771/1000000) 139 96
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t78 : ((-2956943997/5000000000000 : ℚ) : ℝ) ≤ stT139 78 := by
  have hc : ((-5223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2956943997/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-5223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c79 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-979041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7341237/10000000) (δ := 1421/200000000) (ψ := 820771/1000000) 139 97
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t79 : ((-34423860469/312500000000 : ℚ) : ℝ) ≤ stT139 79 := by
  have hc : ((-979091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34423860469/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-979091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c80 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((373477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -371263/1250000) (δ := 1421/200000000) (ψ := 820771/1000000) 139 97
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t80 : ((417503709091/10000000000000 : ℚ) : ℝ) ≤ stT139 80 := by
  have hc : ((373427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((417503709091/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((373427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c81 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((53649/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 269343/2000000) (δ := 1401/200000000) (ψ := 820771/1000000) 139 97
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t81 : ((476852174537/5000000000000 : ℚ) : ℝ) ≤ stT139 81 := by
  have hc : ((429167/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((476852174537/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((429167/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c82 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-311837/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 224423/400000) (δ := 3499/500000000) (ψ := 820771/1000000) 139 97
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t82 : ((-43049274549/625000000000 : ℚ) : ℝ) ≤ stT139 82 := by
  have hc : ((-155931/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43049274549/625000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-155931/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c83 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-705611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2942601/5000000) (δ := 3499/500000000) (ψ := 820771/1000000) 139 98
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t83 : ((-774563857023/10000000000000 : ℚ) : ℝ) ≤ stT139 83 := by
  have hc : ((-705661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-774563857023/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-705661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c84 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((77163/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -172349/1000000) (δ := 6999/500000000) (ψ := 820771/1000000) 139 98
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t84 : ((42093122531/500000000000 : ℚ) : ℝ) ≤ stT139 84 := by
  have hc : ((38579/50000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42093122531/500000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((38579/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c85 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((4617/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1194491/5000000) (δ := 1421/200000000) (ψ := 820771/1000000) 139 98
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t85 : ((6259255529/100000000000 : ℚ) : ℝ) ≤ stT139 85 := by
  have hc : ((23083/40000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6259255529/100000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((23083/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c86 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-847119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3226671/5000000) (δ := 1421/200000000) (ψ := 820771/1000000) 139 98
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t86 : ((-114190756679/1250000000000 : ℚ) : ℝ) ≤ stT139 86 := by
  have hc : ((-847169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114190756679/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-847169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c87 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-500423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5237209/10000000) (δ := 6991/1000000000) (ψ := 820771/1000000) 139 99
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t87 : ((-536563609449/10000000000000 : ℚ) : ℝ) ≤ stT139 87 := by
  have hc : ((-500473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-536563609449/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-500473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c88 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((218637/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -158217/1250000) (δ := 7091/1000000000) (ψ := 820771/1000000) 139 99
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t88 : ((466108745747/5000000000000 : ℚ) : ℝ) ≤ stT139 88 := by
  have hc : ((437249/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((466108745747/5000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((437249/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c89 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((97017/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2660841/10000000) (δ := 889/125000000) (ψ := 820771/1000000) 139 99
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t89 : ((102827128979/2000000000000 : ℚ) : ℝ) ≤ stT139 89 := by
  have hc : ((97007/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102827128979/2000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((97007/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c90 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-865741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3271781/5000000) (δ := 7091/1000000000) (ψ := 820771/1000000) 139 99
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t90 : ((-912624232563/10000000000000 : ℚ) : ℝ) ≤ stT139 90 := by
  have hc : ((-865791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-912624232563/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-865791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c91 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-8287/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2662289/5000000) (δ := 13919/1000000000) (ψ := 820771/1000000) 139 100
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t91 : ((-55602923313/1000000000000 : ℚ) : ℝ) ≤ stT139 91 := by
  have hc : ((-265209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55602923313/1000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-265209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c92 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((819251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1526733/10000000) (δ := 7019/1000000000) (ψ := 820771/1000000) 139 100
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t92 : ((213519006243/2500000000000 : ℚ) : ℝ) ≤ stT139 92 := by
  have hc : ((819201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213519006243/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((819201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c93 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((1962/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 446011/2000000) (δ := 7119/1000000000) (ψ := 820771/1000000) 139 100
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t93 : ((65098746829/1000000000000 : ℚ) : ℝ) ≤ stT139 93 := by
  have hc : ((62779/100000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65098746829/1000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((62779/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c94 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-361409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5946671/10000000) (δ := 1771/250000000) (ψ := 820771/1000000) 139 100
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t94 : ((-93197744787/1250000000000 : ℚ) : ℝ) ≤ stT139 94 := by
  have hc : ((-180717/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93197744787/1250000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-180717/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c95 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-94959/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1521003/2500000) (δ := 7027/1000000000) (ψ := 820771/1000000) 139 101
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t95 : ((-389729408919/5000000000000 : ℚ) : ℝ) ≤ stT139 95 := by
  have hc : ((-379861/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-389729408919/5000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-379861/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c96 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((139651/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -489047/2000000) (δ := 7127/1000000000) (ψ := 820771/1000000) 139 101
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t96 : ((14251784587/250000000000 : ℚ) : ℝ) ≤ stT139 96 := by
  have hc : ((279277/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14251784587/250000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((279277/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c97 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((895013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 577919/5000000) (δ := 7127/1000000000) (ψ := 820771/1000000) 139 101
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t97 : ((454348551099/5000000000000 : ℚ) : ℝ) ≤ stT139 97 := by
  have hc : ((894963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454348551099/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((894963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c98 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-3119/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4719971/10000000) (δ := 1769/250000000) (ψ := 820771/1000000) 139 101
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t98 : ((-6302344567/200000000000 : ℚ) : ℝ) ≤ stT139 98 := by
  have hc : ((-6239/20000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6302344567/200000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-6239/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c99 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-98761/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7460033/10000000) (δ := 6969/1000000000) (ψ := 820771/1000000) 139 102
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t99 : ((-24815895777/250000000000 : ℚ) : ℝ) ≤ stT139 99 := by
  have hc : ((-49383/50000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24815895777/250000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-49383/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c100 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-649/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1983777/5000000) (δ := 7069/1000000000) (ψ := 820771/1000000) 139 102
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t100 : ((-651/400000 : ℚ) : ℝ) ≤ stT139 100 := by
  have hc : ((-651/40000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-651/400000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-651/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c101 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((979281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -50979/1000000) (δ := 7069/1000000000) (ψ := 820771/1000000) 139 102
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t101 : ((974371076547/10000000000000 : ℚ) : ℝ) ≤ stT139 101 := by
  have hc : ((979231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((974371076547/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((979231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c102 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((394241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 582777/2000000) (δ := 3567/500000000) (ψ := 820771/1000000) 139 102
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t102 : ((390307036077/10000000000000 : ℚ) : ℝ) ≤ stT139 102 := by
  have hc : ((394191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((390307036077/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((394191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c103 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-813913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6304129/10000000) (δ := 7069/1000000000) (ψ := 820771/1000000) 139 102
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t103 : ((-80202216279/1000000000000 : ℚ) : ℝ) ≤ stT139 103 := by
  have hc : ((-813963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80202216279/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-813963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c104 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-374891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1511581/2500000) (δ := 3531/500000000) (ψ := 820771/1000000) 139 103
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t104 : ((-91908876549/1250000000000 : ℚ) : ℝ) ≤ stT139 104 := by
  have hc : ((-93729/125000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91908876549/1250000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-93729/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c105 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((463931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1360461/5000000) (δ := 7141/1000000000) (ψ := 820771/1000000) 139 103
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t105 : ((4527014679/100000000000 : ℚ) : ℝ) ≤ stT139 105 := by
  have hc : ((463881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4527014679/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((463881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c106 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((194771/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 286463/5000000) (δ := 7041/1000000000) (ψ := 820771/1000000) 139 103
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t106 : ((37833687577/400000000000 : ℚ) : ℝ) ≤ stT139 106 := by
  have hc : ((194761/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37833687577/400000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((194761/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c107 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((9109/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3835881/10000000) (δ := 3531/500000000) (ψ := 820771/1000000) 139 103
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t107 : ((1099239253/312500000000 : ℚ) : ℝ) ≤ stT139 107 := by
  have hc : ((18193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1099239253/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((18193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c108 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-475521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1413693/2000000) (δ := 3531/500000000) (ψ := 820771/1000000) 139 103
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t108 : ((-228797307023/2500000000000 : ℚ) : ℝ) ≤ stT139 108 := by
  have hc : ((-237773/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228797307023/2500000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-237773/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c109 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-567853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5436729/10000000) (δ := 1787/250000000) (ψ := 820771/1000000) 139 104
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t109 : ((-543952826781/10000000000000 : ℚ) : ℝ) ≤ stT139 109 := by
  have hc : ((-567903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-543952826781/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-567903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c110 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((61747/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1131593/5000000) (δ := 1411/200000000) (ψ := 820771/1000000) 139 104
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t110 : ((14717162701/250000000000 : ℚ) : ℝ) ≤ stT139 110 := by
  have hc : ((30871/50000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14717162701/250000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((30871/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c111 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((938457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 176331/2000000) (δ := 1787/250000000) (ψ := 820771/1000000) 139 104
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t111 : ((890695572899/10000000000000 : ℚ) : ℝ) ≤ stT139 111 := by
  have hc : ((938407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((890695572899/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((938407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c112 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-28497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3998243/10000000) (δ := 1391/200000000) (ψ := 820771/1000000) 139 104
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t112 : ((-1685900179/625000000000 : ℚ) : ℝ) ≤ stT139 112 := by
  have hc : ((-28547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1685900179/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-28547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c113 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-59583/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7087171/10000000) (δ := 1787/250000000) (ψ := 820771/1000000) 139 104
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t113 : ((-448431352769/5000000000000 : ℚ) : ℝ) ≤ stT139 113 := by
  have hc : ((-476689/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-448431352769/5000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-476689/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c114 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-607451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5559109/10000000) (δ := 1411/200000000) (ψ := 820771/1000000) 139 105
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t114 : ((-284488465793/5000000000000 : ℚ) : ℝ) ≤ stT139 114 := by
  have hc : ((-607501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284488465793/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-607501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c115 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((532149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2524149/10000000) (δ := 1787/250000000) (ψ := 820771/1000000) 139 105
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t115 : ((62023055737/1250000000000 : ℚ) : ℝ) ≤ stT139 115 := by
  have hc : ((532099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62023055737/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((532099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c116 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((981279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 242253/5000000) (δ := 1787/250000000) (ψ := 820771/1000000) 139 105
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t116 : ((227761894251/2500000000000 : ℚ) : ℝ) ≤ stT139 116 := by
  have hc : ((981229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227761894251/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((981229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c117 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((45703/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3467377/10000000) (δ := 1391/200000000) (ψ := 820771/1000000) 139 105
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t117 : ((168963469/10000000000 : ℚ) : ℝ) ≤ stT139 117 := by
  have hc : ((91381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168963469/10000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((91381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c118 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-841007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1284969/2000000) (δ := 881/125000000) (ψ := 820771/1000000) 139 105
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t118 : ((-30970241911/400000000000 : ℚ) : ℝ) ≤ stT139 118 := by
  have hc : ((-841057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30970241911/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-841057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c119 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-824579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1270127/2000000) (δ := 6963/1000000000) (ψ := 820771/1000000) 139 106
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t119 : ((-755936579671/10000000000000 : ℚ) : ℝ) ≤ stT139 119 := by
  have hc : ((-824629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-755936579671/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-824629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c120 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((96263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3442651/10000000) (δ := 11/1562500) (ψ := 820771/1000000) 139 106
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t120 : ((4392639153/250000000000 : ℚ) : ℝ) ≤ stT139 120 := by
  have hc : ((48119/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4392639153/250000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((48119/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c121 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((487561/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -279409/5000000) (δ := 11/1562500) (ψ := 820771/1000000) 139 106
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t121 : ((2770088139/31250000000 : ℚ) : ℝ) ≤ stT139 121 := by
  have hc : ((30471/31250 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2770088139/31250000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((30471/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c122 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((151353/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2301281/10000000) (δ := 6963/1000000000) (ψ := 820771/1000000) 139 106
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t122 : ((274034362117/5000000000000 : ℚ) : ℝ) ≤ stT139 122 := by
  have hc : ((302681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274034362117/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((302681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c123 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-465691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1284507/2500000) (δ := 7063/1000000000) (ψ := 820771/1000000) 139 106
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t123 : ((-41994468747/1000000000000 : ℚ) : ℝ) ≤ stT139 123 := by
  have hc : ((-465741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41994468747/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-465741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c124 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-199847/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7756159/10000000) (δ := 7133/1000000000) (ψ := 820771/1000000) 139 107
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t124 : ((-179476982139/2000000000000 : ℚ) : ℝ) ≤ stT139 124 := by
  have hc : ((-199857/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179476982139/2000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-199857/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c125 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-80673/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4964969/10000000) (δ := 697/100000000) (ψ := 820771/1000000) 139 107
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t125 : ((-18041283581/500000000000 : ℚ) : ℝ) ≤ stT139 125 := by
  have hc : ((-80683/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18041283581/500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-80683/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c126 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((638377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -109801/500000) (δ := 7133/1000000000) (ψ := 820771/1000000) 139 107
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t126 : ((56866637449/1000000000000 : ℚ) : ℝ) ≤ stT139 126 := by
  have hc : ((638327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56866637449/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((638327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c127 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((97581/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 551003/10000000) (δ := 707/100000000) (ψ := 820771/1000000) 139 107
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t127 : ((2705770283/31250000000 : ℚ) : ℝ) ≤ stT139 127 := by
  have hc : ((12197/12500 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2705770283/31250000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((12197/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c128 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((16079/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 655303/2000000) (δ := 707/100000000) (ψ := 820771/1000000) 139 107
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t128 : ((113673540981/5000000000000 : ℚ) : ℝ) ≤ stT139 128 := by
  have hc : ((128607/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113673540981/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((128607/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c129 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-22881/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5980829/10000000) (δ := 7033/1000000000) (ψ := 820771/1000000) 139 107
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t129 : ((-322351600571/5000000000000 : ℚ) : ℝ) ≤ stT139 129 := by
  have hc : ((-366121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-322351600571/5000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-366121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c130 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-947939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7043739/10000000) (δ := 6977/1000000000) (ψ := 820771/1000000) 139 108
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t130 : ((-831442284351/10000000000000 : ℚ) : ℝ) ≤ stT139 130 := by
  have hc : ((-947989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-831442284351/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-947989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c131 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-2257/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4380881/10000000) (δ := 7077/1000000000) (ψ := 820771/1000000) 139 108
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t131 : ((-3155997201/200000000000 : ℚ) : ℝ) ≤ stT139 131 := by
  have hc : ((-18061/100000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3155997201/200000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-18061/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c132 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((767853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1738283/10000000) (δ := 3513/500000000) (ψ := 820771/1000000) 139 108
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t132 : ((167071629391/2500000000000 : ℚ) : ℝ) ≤ stT139 132 := by
  have hc : ((767803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167071629391/2500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((767803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c133 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((938081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 884369/10000000) (δ := 3513/500000000) (ψ := 820771/1000000) 139 108
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t133 : ((813375122379/10000000000000 : ℚ) : ℝ) ≤ stT139 133 := by
  have hc : ((938031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((813375122379/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((938031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c134 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((174943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 348737/1000000) (δ := 6963/500000000) (ψ := 820771/1000000) 139 108
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t134 : ((37771116531/2500000000000 : ℚ) : ℝ) ≤ stT139 134 := by
  have hc : ((174893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37771116531/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((174893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c135 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-756281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1214203/2000000) (δ := 3513/500000000) (ψ := 820771/1000000) 139 108
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t135 : ((-650946107453/10000000000000 : ℚ) : ℝ) ≤ stT139 135 := by
  have hc : ((-756331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-650946107453/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-756331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c136 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-951523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7072363/10000000) (δ := 1771/250000000) (ψ := 820771/1000000) 139 109
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t136 : ((-815967186489/10000000000000 : ℚ) : ℝ) ≤ stT139 136 := by
  have hc : ((-951573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-815967186489/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-951573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c137 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-237529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -282909/625000) (δ := 7119/1000000000) (ψ := 820771/1000000) 139 109
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t137 : ((-101488759641/5000000000000 : ℚ) : ℝ) ≤ stT139 137 := by
  have hc : ((-237579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101488759641/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-237579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c138 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((696913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24991/125000) (δ := 1771/250000000) (ψ := 820771/1000000) 139 109
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t138 : ((74151101241/1250000000000 : ℚ) : ℝ) ≤ stT139 138 := by
  have hc : ((696863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74151101241/1250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((696863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c139 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((489641/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 254887/5000000) (δ := 873/125000000) (ψ := 820771/1000000) 139 109
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t139 : ((6488850247/78125000000 : ℚ) : ℝ) ≤ stT139 139 := by
  have hc : ((30601/31250 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6488850247/78125000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((30601/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c140 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((362049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 750207/2500000) (δ := 1771/250000000) (ψ := 820771/1000000) 139 109
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t140 : ((152972451423/5000000000000 : ℚ) : ℝ) ≤ stT139 140 := by
  have hc : ((361999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152972451423/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((361999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c141 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-580101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1368531/2500000) (δ := 7019/1000000000) (ψ := 820771/1000000) 139 109
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t141 : ((-61071915619/1250000000000 : ℚ) : ℝ) ≤ stT139 141 := by
  have hc : ((-580151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61071915619/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-580151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c142 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-499769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7777987/10000000) (δ := 6991/1000000000) (ψ := 820771/1000000) 139 110
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t142 : ((-104854532127/1250000000000 : ℚ) : ℝ) ≤ stT139 142 := by
  have hc : ((-249897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104854532127/1250000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-249897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c143 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-4283/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5339371/10000000) (δ := 6991/1000000000) (ψ := 820771/1000000) 139 110
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t143 : ((-17909816331/400000000000 : ℚ) : ℝ) ≤ stT139 143 := by
  have hc : ((-21417/40000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17909816331/400000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-21417/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c144 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((49101/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2917783/10000000) (δ := 889/125000000) (ψ := 820771/1000000) 139 110
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t144 : ((163649101207/5000000000000 : ℚ) : ℝ) ≤ stT139 144 := by
  have hc : ((196379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163649101207/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((196379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c145 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((244757/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -512909/10000000) (δ := 1753/250000000) (ψ := 820771/1000000) 139 110
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t145 : ((203249049003/2500000000000 : ℚ) : ℝ) ≤ stT139 145 := by
  have hc : ((489489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203249049003/2500000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((489489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c146 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((731573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58607/312500) (δ := 6991/1000000000) (ψ := 820771/1000000) 139 110
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t146 : ((121082418483/2000000000000 : ℚ) : ℝ) ≤ stT139 146 := by
  have hc : ((731523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121082418483/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((731523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c147 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-127823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33183/78125) (δ := 1753/250000000) (ψ := 820771/1000000) 139 110
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t147 : ((-105467988051/10000000000000 : ℚ) : ℝ) ≤ stT139 147 := by
  have hc : ((-127873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105467988051/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-127873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c148 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-175493/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 660337/1000000) (δ := 6991/1000000000) (ψ := 820771/1000000) 139 110
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t148 : ((-28852517697/400000000000 : ℚ) : ℝ) ≤ stT139 148 := by
  have hc : ((-175503/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28852517697/400000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-175503/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c149 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-181307/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3382247/5000000) (δ := 1421/200000000) (ψ := 820771/1000000) 139 111
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t149 : ((-4641896517/62500000000 : ℚ) : ℝ) ≤ stT139 149 := by
  have hc : ((-181317/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4641896517/62500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-181317/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c150 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-101903/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4440101/10000000) (δ := 1401/200000000) (ψ := 820771/1000000) 139 111
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t150 : ((-10402988277/625000000000 : ℚ) : ℝ) ≤ stT139 150 := by
  have hc : ((-12741/62500 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10402988277/625000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-12741/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c151 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((658147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1065551/5000000) (δ := 3549/500000000) (ψ := 820771/1000000) 139 111
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t151 : ((133887860359/2500000000000 : ℚ) : ℝ) ≤ stT139 151 := by
  have hc : ((658097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133887860359/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((658097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c152 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((199577/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 162641/10000000) (δ := 3499/500000000) (ψ := 820771/1000000) 139 111
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t152 : ((161870190669/2000000000000 : ℚ) : ℝ) ≤ stT139 152 := by
  have hc : ((199567/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161870190669/2000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((199567/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c153 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((559897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2441337/10000000) (δ := 1421/200000000) (ψ := 820771/1000000) 139 111
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t153 : ((113152356711/2500000000000 : ℚ) : ℝ) ≤ stT139 153 := by
  have hc : ((559847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113152356711/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((559847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c154 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-306279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1176299/2500000) (δ := 3549/500000000) (ψ := 820771/1000000) 139 111
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t154 : ((-246846953767/10000000000000 : ℚ) : ℝ) ≤ stT139 154 := by
  have hc : ((-306329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246846953767/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-306329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c155 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-467977/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6954389/10000000) (δ := 1421/200000000) (ψ := 820771/1000000) 139 111
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t155 : ((-9397714161/125000000000 : ℚ) : ℝ) ≤ stT139 155 := by
  have hc : ((-234001/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9397714161/125000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-234001/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c156 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-215187/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1629709/2500000) (δ := 3503/500000000) (ψ := 820771/1000000) 139 112
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t156 : ((-344595085759/5000000000000 : ℚ) : ℝ) ≤ stT139 156 := by
  have hc : ((-430399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-344595085759/5000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-430399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c157 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-14801/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4298381/10000000) (δ := 7097/1000000000) (ψ := 820771/1000000) 139 112
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t157 : ((-5908238061/500000000000 : ℚ) : ℝ) ≤ stT139 157 := by
  have hc : ((-7403/50000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5908238061/500000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-7403/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c158 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((83729/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1046017/5000000) (δ := 7097/1000000000) (ψ := 820771/1000000) 139 112
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t158 : ((266424879287/5000000000000 : ℚ) : ℝ) ≤ stT139 158 := by
  have hc : ((334891/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((266424879287/5000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((334891/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c159 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((999193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 100413/10000000) (δ := 7097/1000000000) (ψ := 820771/1000000) 139 112
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t159 : ((792371355293/10000000000000 : ℚ) : ℝ) ≤ stT139 159 := by
  have hc : ((999143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((792371355293/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((999143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c160 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((12249/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2279099/10000000) (δ := 7097/1000000000) (ψ := 820771/1000000) 139 112
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t160 : ((1210361139/25000000000 : ℚ) : ℝ) ≤ stT139 160 := by
  have hc : ((1531/2500 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1210361139/25000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((1531/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c161 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-20541/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2222099/5000000) (δ := 6997/1000000000) (ψ := 820771/1000000) 139 112
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t161 : ((-8096264303/500000000000 : ℚ) : ℝ) ≤ stT139 161 := by
  have hc : ((-10273/50000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8096264303/500000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-10273/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c162 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-13688/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3297959/5000000) (δ := 6997/1000000000) (ψ := 820771/1000000) 139 112
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t162 : ((-13766314507/200000000000 : ℚ) : ℝ) ≤ stT139 162 := by
  have hc : ((-438041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13766314507/200000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-438041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c163 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-234657/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1394713/2000000) (δ := 699/100000000) (ψ := 820771/1000000) 139 113
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t163 : ((-367614934479/5000000000000 : ℚ) : ℝ) ≤ stT139 163 := by
  have hc : ((-469339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-367614934479/5000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-469339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c164 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-90049/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -969637/2000000) (δ := 7113/1000000000) (ψ := 820771/1000000) 139 113
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t164 : ((-140652466887/5000000000000 : ℚ) : ℝ) ≤ stT139 164 := by
  have hc : ((-180123/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140652466887/5000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-180123/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c165 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((18347/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2735733/10000000) (δ := 699/100000000) (ψ := 820771/1000000) 139 113
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t165 : ((1428154581/40000000000 : ℚ) : ℝ) ≤ stT139 165 := by
  have hc : ((3669/8000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1428154581/40000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((3669/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c166 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((967811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -318017/5000000) (δ := 709/100000000) (ψ := 820771/1000000) 139 113
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t166 : ((15022554003/200000000000 : ℚ) : ℝ) ≤ stT139 166 := by
  have hc : ((967761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15022554003/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((967761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c167 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((33449/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 725543/5000000) (δ := 699/100000000) (ψ := 820771/1000000) 139 113
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t167 : ((25882057881/400000000000 : ℚ) : ℝ) ≤ stT139 167 := by
  have hc : ((33447/40000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25882057881/400000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((33447/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c168 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((159829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55089/156250) (δ := 7013/1000000000) (ψ := 820771/1000000) 139 113
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t168 : ((30818013741/2500000000000 : ℚ) : ℝ) ≤ stT139 168 := by
  have hc : ((159779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30818013741/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((159779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c169 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-308301/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5588039/10000000) (δ := 7013/1000000000) (ψ := 820771/1000000) 139 113
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t169 : ((-118586958653/2500000000000 : ℚ) : ℝ) ≤ stT139 169 := by
  have hc : ((-154163/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118586958653/2500000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-154163/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c170 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-996277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1527637/2000000) (δ := 7113/1000000000) (ψ := 820771/1000000) 139 113
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t170 : ((-152829587511/2000000000000 : ℚ) : ℝ) ≤ stT139 170 := by
  have hc : ((-996327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152829587511/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-996327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c171 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-745887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -753957/1250000) (δ := 89/12500000) (ψ := 820771/1000000) 139 114
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t171 : ((-7130411783/125000000000 : ℚ) : ℝ) ≤ stT139 171 := by
  have hc : ((-745937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7130411783/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-745937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c172 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-15683/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4005419/10000000) (δ := 7083/1000000000) (ψ := 820771/1000000) 139 114
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t172 : ((-2994310011/1250000000000 : ℚ) : ℝ) ≤ stT139 172 := by
  have hc : ((-3927/125000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2994310011/1250000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-3927/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c173 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((349653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -995463/5000000) (δ := 89/12500000) (ψ := 820771/1000000) 139 114
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t173 : ((13290846199/250000000000 : ℚ) : ℝ) ≤ stT139 173 := by
  have hc : ((87407/125000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13290846199/250000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((87407/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c174 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((999989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11959/10000000) (δ := 7083/1000000000) (ψ := 820771/1000000) 139 114
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t174 : ((379025878011/5000000000000 : ℚ) : ℝ) ≤ stT139 174 := by
  have hc : ((999939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((379025878011/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((999939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c175 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((695737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1001689/5000000) (δ := 89/12500000) (ψ := 820771/1000000) 139 114
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t175 : ((65736160317/1250000000000 : ℚ) : ℝ) ≤ stT139 175 := by
  have hc : ((695687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65736160317/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((695687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c176 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-903/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3983433/10000000) (δ := 89/12500000) (ψ := 820771/1000000) 139 114
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t176 : ((-136433999/80000000000 : ℚ) : ℝ) ≤ stT139 176 := by
  have hc : ((-181/8000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136433999/80000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-181/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c177 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-181093/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2976149/5000000) (δ := 6983/1000000000) (ψ := 820771/1000000) 139 114
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t177 : ((-272254811517/5000000000000 : ℚ) : ℝ) ≤ stT139 177 := by
  have hc : ((-362211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272254811517/5000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-362211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c178 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-999749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48737/62500) (δ := 1769/250000000) (ψ := 820771/1000000) 139 115
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t178 : ((-187345336017/2500000000000 : ℚ) : ℝ) ≤ stT139 178 := by
  have hc : ((-999799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187345336017/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-999799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c179 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-139177/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73139/125000) (δ := 7127/1000000000) (ψ := 820771/1000000) 139 115
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t179 : ((-26008343633/500000000000 : ℚ) : ℝ) ≤ stT139 179 := by
  have hc : ((-139187/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26008343633/500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-139187/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c180 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((4717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1957599/5000000) (δ := 109/15625000) (ψ := 820771/1000000) 139 115
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t180 : ((695714357/2000000000000 : ℚ) : ℝ) ≤ stT139 180 := by
  have hc : ((4667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((695714357/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((4667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c181 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((699577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -994989/5000000) (δ := 7127/1000000000) (ψ := 820771/1000000) 139 115
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t181 : ((259977110969/5000000000000 : ℚ) : ℝ) ≤ stT139 181 := by
  have hc : ((699527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((259977110969/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((699527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c182 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((199909/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -589/78125) (δ := 7127/1000000000) (ψ := 820771/1000000) 139 115
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t182 : ((148174933851/2000000000000 : ℚ) : ℝ) ≤ stT139 182 := by
  have hc : ((199899/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148174933851/2000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((199899/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c183 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((372089/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 914367/5000000) (δ := 7027/1000000000) (ψ := 820771/1000000) 139 115
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t183 : ((8594922567/156250000000 : ℚ) : ℝ) ≤ stT139 183 := by
  have hc : ((11627/15625 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8594922567/156250000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((11627/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c184 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((81717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 372247/1000000) (δ := 7027/1000000000) (ψ := 820771/1000000) 139 115
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t184 : ((60205647403/10000000000000 : ℚ) : ℝ) ≤ stT139 184 := by
  have hc : ((81667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60205647403/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((81667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c185 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-155557/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1121191/2000000) (δ := 7127/1000000000) (ψ := 820771/1000000) 139 115
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t185 : ((-45750811977/1000000000000 : ℚ) : ℝ) ≤ stT139 185 := by
  have hc : ((-311139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45750811977/1000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-311139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c186 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-247197/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3739629/5000000) (δ := 7127/1000000000) (ψ := 820771/1000000) 139 115
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t186 : ((-90631452471/1250000000000 : ℚ) : ℝ) ≤ stT139 186 := by
  have hc : ((-494419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90631452471/1250000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-494419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c187 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-206977/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6365411/10000000) (δ := 7069/1000000000) (ψ := 820771/1000000) 139 116
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t187 : ((-302731665267/5000000000000 : ℚ) : ℝ) ≤ stT139 187 := by
  have hc : ((-413979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-302731665267/5000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-413979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c188 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-231909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4512089/10000000) (δ := 6969/1000000000) (ψ := 820771/1000000) 139 116
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t188 : ((-6766939907/400000000000 : ℚ) : ℝ) ≤ stT139 188 := by
  have hc : ((-231959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6766939907/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-231959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c189 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((24119/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2668567/10000000) (δ := 7069/1000000000) (ψ := 820771/1000000) 139 116
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t189 : ((1096384323/31250000000 : ℚ) : ℝ) ≤ stT139 189 := by
  have hc : ((48233/100000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1096384323/31250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((48233/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c190 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((236191/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -834809/10000000) (δ := 3517/500000000) (ψ := 820771/1000000) 139 116
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t190 : ((85670916733/1250000000000 : ℚ) : ℝ) ≤ stT139 190 := by
  have hc : ((472357/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85670916733/1250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((472357/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c191 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((92271/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 989357/10000000) (δ := 7069/1000000000) (ψ := 820771/1000000) 139 116
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t191 : ((16690319671/250000000000 : ℚ) : ℝ) ≤ stT139 191 := by
  have hc : ((46133/50000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16690319671/250000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((46133/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c192 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((434253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21906/78125) (δ := 3567/500000000) (ψ := 820771/1000000) 139 116
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t192 : ((313358660461/10000000000000 : ℚ) : ℝ) ≤ stT139 192 := by
  have hc : ((434203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((313358660461/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((434203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c193 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-53899/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4609161/10000000) (δ := 3567/500000000) (ψ := 820771/1000000) 139 116
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t193 : ((-4850570093/250000000000 : ℚ) : ℝ) ≤ stT139 193 := by
  have hc : ((-53909/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4850570093/250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-53909/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c194 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-167339/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6405041/10000000) (δ := 3567/500000000) (ψ := 820771/1000000) 139 116
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t194 : ((-120149720691/2000000000000 : ℚ) : ℝ) ≤ stT139 194 := by
  have hc : ((-167349/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120149720691/2000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-167349/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c195 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-990891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3758143/5000000) (δ := 3521/500000000) (ψ := 820771/1000000) 139 117
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t195 : ((-141925542843/2000000000000 : ℚ) : ℝ) ≤ stT139 195 := by
  have hc : ((-990941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141925542843/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-990941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c196 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-26517/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5738789/10000000) (δ := 6961/1000000000) (ψ := 820771/1000000) 139 117
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t196 : ((-9471075217/200000000000 : ℚ) : ℝ) ≤ stT139 196 := by
  have hc : ((-26519/40000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9471075217/200000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-26519/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c197 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-8667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3970327/10000000) (δ := 7061/1000000000) (ψ := 820771/1000000) 139 117
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t197 : ((-1548199483/1250000000000 : ℚ) : ℝ) ≤ stT139 197 := by
  have hc : ((-2173/125000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1548199483/1250000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-2173/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c198 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((316903/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -221083/1000000) (δ := 6961/1000000000) (ψ := 820771/1000000) 139 117
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t198 : ((112597685691/2500000000000 : ℚ) : ℝ) ≤ stT139 198 := by
  have hc : ((158439/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112597685691/2500000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((158439/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c199 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((491553/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -230097/5000000) (δ := 3571/500000000) (ψ := 820771/1000000) 139 117
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t199 : ((43554357521/625000000000 : ℚ) : ℝ) ≤ stT139 199 := by
  have hc : ((61441/62500 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43554357521/625000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((61441/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c200 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((871443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1281649/10000000) (δ := 7061/1000000000) (ψ := 820771/1000000) 139 117
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t200 : ((308083609329/5000000000000 : ℚ) : ℝ) ≤ stT139 200 := by
  have hc : ((871393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((308083609329/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((871393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c201 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((356819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75371/250000) (δ := 7061/1000000000) (ψ := 820771/1000000) 139 117
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t201 : ((50329046061/2000000000000 : ℚ) : ℝ) ≤ stT139 201 := by
  have hc : ((356769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50329046061/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((356769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c202 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-159633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4739379/10000000) (δ := 3571/500000000) (ψ := 820771/1000000) 139 117
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t202 : ((-28083762371/1250000000000 : ℚ) : ℝ) ≤ stT139 202 := by
  have hc : ((-79829/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28083762371/1250000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-79829/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c203 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-211891/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3227719/5000000) (δ := 3521/500000000) (ψ := 820771/1000000) 139 117
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t203 : ((-297454452441/5000000000000 : ℚ) : ℝ) ≤ stT139 203 := by
  have hc : ((-423807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-297454452441/5000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-423807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c204 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-62023/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -754491/1000000) (δ := 7149/1000000000) (ψ := 820771/1000000) 139 118
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t204 : ((-347416265469/5000000000000 : ℚ) : ℝ) ≤ stT139 204 := by
  have hc : ((-496209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-347416265469/5000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-496209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c205 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-173577/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1169127/2000000) (δ := 7149/1000000000) (ψ := 820771/1000000) 139 118
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t205 : ((-242480576149/5000000000000 : ℚ) : ℝ) ≤ stT139 205 := by
  have hc : ((-347179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242480576149/5000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-347179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c206 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-9093/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4154631/10000000) (δ := 3477/500000000) (ψ := 820771/1000000) 139 118
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t206 : ((-1584721483/250000000000 : ℚ) : ℝ) ≤ stT139 206 := by
  have hc : ((-4549/50000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1584721483/250000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-4549/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c207 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((549751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2471827/10000000) (δ := 7149/1000000000) (ψ := 820771/1000000) 139 118
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t207 : ((47758572581/1250000000000 : ℚ) : ℝ) ≤ stT139 207 := by
  have hc : ((549701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47758572581/1250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((549701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c208 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((949597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -797121/10000000) (δ := 3527/500000000) (ψ := 820771/1000000) 139 118
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t208 : ((5267137209/80000000000 : ℚ) : ℝ) ≤ stT139 208 := by
  have hc : ((949547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5267137209/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((949547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c209 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((940117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 869559/10000000) (δ := 7049/1000000000) (ψ := 820771/1000000) 139 118
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t209 : ((325128752419/5000000000000 : ℚ) : ℝ) ≤ stT139 209 := by
  have hc : ((940067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((325128752419/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((940067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c210 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((530749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2528281/10000000) (δ := 7149/1000000000) (ψ := 820771/1000000) 139 118
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t210 : ((73243361087/2000000000000 : ℚ) : ℝ) ≤ stT139 210 := by
  have hc : ((530699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73243361087/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((530699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c211 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-50339/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2089557/5000000) (δ := 3477/500000000) (ψ := 820771/1000000) 139 118
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t211 : ((-8668009539/1250000000000 : ℚ) : ℝ) ≤ stT139 211 := by
  have hc : ((-12591/125000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8668009539/1250000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-12591/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c212 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-687511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5822129/10000000) (δ := 7049/1000000000) (ψ := 820771/1000000) 139 118
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t212 : ((-472218957483/10000000000000 : ℚ) : ℝ) ≤ stT139 212 := by
  have hc : ((-687561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-472218957483/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-687561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c213 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-493723/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7457429/10000000) (δ := 3477/500000000) (ψ := 820771/1000000) 139 118
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t213 : ((-84577674593/1250000000000 : ℚ) : ℝ) ≤ stT139 213 := by
  have hc : ((-123437/125000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84577674593/1250000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-123437/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c214 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-881181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6622879/10000000) (δ := 1739/250000000) (ψ := 820771/1000000) 139 119
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t214 : ((-301198587183/5000000000000 : ℚ) : ℝ) ≤ stT139 214 := by
  have hc : ((-881231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-301198587183/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-881231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c215 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-417177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2501417/5000000) (δ := 1739/250000000) (ψ := 820771/1000000) 139 119
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t215 : ((-56909345573/2000000000000 : ℚ) : ℝ) ≤ stT139 215 := by
  have hc : ((-417227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56909345573/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-417227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c216 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((213033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -678059/2000000) (δ := 1739/250000000) (ψ := 820771/1000000) 139 119
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t216 : ((144916401979/10000000000000 : ℚ) : ℝ) ≤ stT139 216 := by
  have hc : ((212983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144916401979/10000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((212983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c217 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((755689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1785227/10000000) (δ := 441/62500000) (ψ := 820771/1000000) 139 119
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t217 : ((128240250329/2500000000000 : ℚ) : ℝ) ≤ stT139 217 := by
  have hc : ((755639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128240250329/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((755639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c218 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((249297/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -187527/10000000) (δ := 7147/1000000000) (ψ := 820771/1000000) 139 119
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t218 : ((67534661033/1000000000000 : ℚ) : ℝ) ≤ stT139 218 := by
  have hc : ((498569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67534661033/1000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((498569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c219 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((846643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1402877/10000000) (δ := 441/62500000) (ψ := 820771/1000000) 139 119
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t219 : ((572074214041/10000000000000 : ℚ) : ℝ) ≤ stT139 219 := by
  have hc : ((846593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((572074214041/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((846593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c220 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((73513/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2986017/10000000) (δ := 7047/1000000000) (ψ := 820771/1000000) 139 119
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t220 : ((49555649097/2000000000000 : ℚ) : ℝ) ≤ stT139 220 := by
  have hc : ((73503/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49555649097/2000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((73503/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c221 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-251281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4561999/10000000) (δ := 7047/1000000000) (ψ := 820771/1000000) 139 119
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t221 : ((-169063577763/10000000000000 : ℚ) : ℝ) ≤ stT139 221 := by
  have hc : ((-251331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169063577763/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-251331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c222 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-154343/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6130823/10000000) (δ := 441/62500000) (ψ := 820771/1000000) 139 119
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t222 : ((-103595096421/2000000000000 : ℚ) : ℝ) ≤ stT139 222 := by
  have hc : ((-154353/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103595096421/2000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-154353/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c223 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-498959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7692627/10000000) (δ := 441/62500000) (ψ := 820771/1000000) 139 119
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t223 : ((-835361589/12500000000 : ℚ) : ℝ) ≤ stT139 223 := by
  have hc : ((-62373/62500 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-835361589/12500000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-62373/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c224 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-848641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6460517/10000000) (δ := 7063/1000000000) (ψ := 820771/1000000) 139 120
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t224 : ((-283528143207/5000000000000 : ℚ) : ℝ) ≤ stT139 224 := by
  have hc : ((-848691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283528143207/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-848691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c225 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-76823/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4912613/10000000) (δ := 7063/1000000000) (ψ := 820771/1000000) 139 120
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t225 : ((-51222025611/2000000000000 : ℚ) : ℝ) ≤ stT139 225 := by
  have hc : ((-76833/200000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51222025611/2000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-76833/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c226 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((220331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3371607/10000000) (δ := 13963/1000000000) (ψ := 820771/1000000) 139 120
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t226 : ((14652871839/1000000000000 : ℚ) : ℝ) ≤ stT139 226 := by
  have hc : ((220281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14652871839/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((220281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c227 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((92733/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1837377/10000000) (δ := 7063/1000000000) (ψ := 820771/1000000) 139 120
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t227 : ((246179506761/5000000000000 : ℚ) : ℝ) ≤ stT139 227 := by
  have hc : ((370907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((246179506761/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((370907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c228 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((496163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -154953/5000000) (δ := 7063/1000000000) (ψ := 820771/1000000) 139 120
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t228 : ((82143832177/1250000000000 : ℚ) : ℝ) ≤ stT139 228 := by
  have hc : ((248069/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82143832177/1250000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((248069/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c229 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((442487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1210893/10000000) (δ := 7063/1000000000) (ψ := 820771/1000000) 139 120
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t229 : ((73096713479/1250000000000 : ℚ) : ℝ) ≤ stT139 229 := by
  have hc : ((221231/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73096713479/1250000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((221231/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c230 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((231233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1362527/5000000) (δ := 357/50000000) (ψ := 820771/1000000) 139 120
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t230 : ((952837069/31250000000 : ℚ) : ℝ) ≤ stT139 230 := by
  have hc : ((28901/62500 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((952837069/31250000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((28901/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c231 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-60979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 529081/1250000) (δ := 357/50000000) (ψ := 820771/1000000) 139 120
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t231 : ((-313575811/39062500000 : ℚ) : ℝ) ≤ stT139 231 := by
  have hc : ((-15251/125000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-313575811/39062500000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-15251/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c232 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-661403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5733709/10000000) (δ := 357/50000000) (ψ := 820771/1000000) 139 120
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t232 : ((-434265722449/10000000000000 : ℚ) : ℝ) ≤ stT139 232 := by
  have hc : ((-661453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-434265722449/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-661453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c233 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-968849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3614171/5000000) (δ := 7063/1000000000) (ψ := 820771/1000000) 139 120
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t233 : ((-317373525339/5000000000000 : ℚ) : ℝ) ≤ stT139 233 := by
  have hc : ((-968899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-317373525339/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-968899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c234 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-470531/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6991383/10000000) (δ := 707/100000000) (ψ := 820771/1000000) 139 121
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t234 : ((-76903084719/1250000000000 : ℚ) : ℝ) ≤ stT139 234 := by
  have hc : ((-117639/125000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76903084719/1250000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-117639/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c235 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-59157/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43043/78125) (δ := 707/100000000) (ψ := 820771/1000000) 139 121
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t235 : ((-19296544149/500000000000 : ℚ) : ℝ) ≤ stT139 235 := by
  have hc : ((-29581/50000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19296544149/500000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-29581/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c236 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-42757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -806783/2000000) (δ := 697/100000000) (ψ := 820771/1000000) 139 121
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t236 : ((-5573000523/2000000000000 : ℚ) : ℝ) ≤ stT139 236 := by
  have hc : ((-42807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5573000523/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-42807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c237 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((518387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2564581/10000000) (δ := 7033/1000000000) (ψ := 820771/1000000) 139 121
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t237 : ((336695646753/10000000000000 : ℚ) : ℝ) ≤ stT139 237 := by
  have hc : ((518337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((336695646753/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((518337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c238 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((226127/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137679/1250000) (δ := 697/100000000) (ψ := 820771/1000000) 139 121
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t238 : ((293136194487/5000000000000 : ℚ) : ℝ) ≤ stT139 238 := by
  have hc : ((452229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((293136194487/5000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((452229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c239 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((989901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 355601/10000000) (δ := 707/100000000) (ψ := 820771/1000000) 139 121
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t239 : ((320140579973/5000000000000 : ℚ) : ℝ) ≤ stT139 239 := by
  have hc : ((989851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320140579973/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((989851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c240 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((30003/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 225819/1250000) (δ := 7033/1000000000) (ψ := 820771/1000000) 139 121
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t240 : ((19365555497/400000000000 : ℚ) : ℝ) ≤ stT139 240 := by
  have hc : ((30001/40000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19365555497/400000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((30001/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c241 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((266937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3251457/10000000) (δ := 7033/1000000000) (ψ := 820771/1000000) 139 121
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t241 : ((42979215593/2500000000000 : ℚ) : ℝ) ≤ stT139 241 := by
  have hc : ((266887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42979215593/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((266887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c242 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-150317/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 938077/2000000) (δ := 7033/1000000000) (ψ := 820771/1000000) 139 121
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t242 : ((-1932871923/100000000000 : ℚ) : ℝ) ≤ stT139 242 := by
  have hc : ((-75171/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1932871923/100000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-75171/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c243 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-96227/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6123371/10000000) (δ := 697/100000000) (ψ := 820771/1000000) 139 121
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t243 : ((-246934904433/5000000000000 : ℚ) : ℝ) ≤ stT139 243 := by
  have hc : ((-384933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246934904433/5000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-384933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c244 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-3102/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1887621/2500000) (δ := 697/100000000) (ψ := 820771/1000000) 139 121
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t244 : ((-12710104953/200000000000 : ℚ) : ℝ) ≤ stT139 244 := by
  have hc : ((-99269/100000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12710104953/200000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-99269/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c245 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-901703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3368111/5000000) (δ := 7013/500000000) (ψ := 820771/1000000) 139 122
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t245 : ((-576109251381/10000000000000 : ℚ) : ℝ) ≤ stT139 245 := by
  have hc : ((-901753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-576109251381/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-901753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c246 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((-66133/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5320733/10000000) (δ := 3563/500000000) (ψ := 820771/1000000) 139 122
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t246 : ((-168675458389/5000000000000 : ℚ) : ℝ) ≤ stT139 246 := by
  have hc : ((-264557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168675458389/5000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-264557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c247 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((3199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -782199/2000000) (δ := 3563/500000000) (ψ := 820771/1000000) 139 122
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t247 : ((252445677/625000000000 : ℚ) : ℝ) ≤ stT139 247 := by
  have hc : ((1587/250000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252445677/625000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((1587/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c248 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((537959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -626739/2500000) (δ := 3563/500000000) (ψ := 820771/1000000) 139 122
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t248 : ((68314443/2000000000 : ℚ) : ℝ) ≤ stT139 248 := by
  have hc : ((537909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68314443/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((537909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c249 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((225821/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1108581/10000000) (δ := 3513/500000000) (ψ := 820771/1000000) 139 122
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t249 : ((71550132927/1250000000000 : ℚ) : ℝ) ≤ stT139 249 := by
  have hc : ((451617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71550132927/1250000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((451617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_c250 :
    |Real.cos (((139 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((124193/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 142117/5000000) (δ := 6977/1000000000) (ψ := 820771/1000000) 139 122
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st139_t250 : ((62834024777/1000000000000 : ℚ) : ℝ) ≤ stT139 250 := by
  have hc : ((496747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((139 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st139_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62834024777/1000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((496747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st139_p1 : ((681607/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT139 (i+1) := by
  rw [Finset.sum_range_one]
  exact st139_t1

theorem st139_p2 : ((2212632278243/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT139 (i+1))
      = (∑ i ∈ Finset.range 1, stT139 (i+1)) + stT139 2 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 1
    simpa using h
  have hprev := st139_p1
  have hstep := st139_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p3 : ((1440124147631/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT139 (i+1))
      = (∑ i ∈ Finset.range 2, stT139 (i+1)) + stT139 3 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 2
    simpa using h
  have hprev := st139_p2
  have hstep := st139_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p4 : ((6660497208949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT139 (i+1))
      = (∑ i ∈ Finset.range 3, stT139 (i+1)) + stT139 4 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 3
    simpa using h
  have hprev := st139_p3
  have hstep := st139_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p5 : ((2246673390253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT139 (i+1))
      = (∑ i ∈ Finset.range 4, stT139 (i+1)) + stT139 5 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 4
    simpa using h
  have hprev := st139_p4
  have hstep := st139_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p6 : ((-1831318878447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT139 (i+1))
      = (∑ i ∈ Finset.range 5, stT139 (i+1)) + stT139 6 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 5
    simpa using h
  have hprev := st139_p5
  have hstep := st139_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p7 : ((1455599390781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT139 (i+1))
      = (∑ i ∈ Finset.range 6, stT139 (i+1)) + stT139 7 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 6
    simpa using h
  have hprev := st139_p6
  have hstep := st139_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p8 : ((244134030513/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT139 (i+1))
      = (∑ i ∈ Finset.range 7, stT139 (i+1)) + stT139 8 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 7
    simpa using h
  have hprev := st139_p7
  have hstep := st139_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p9 : ((18929494629/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT139 (i+1))
      = (∑ i ∈ Finset.range 8, stT139 (i+1)) + stT139 9 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 8
    simpa using h
  have hprev := st139_p8
  have hstep := st139_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p10 : ((869978859859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT139 (i+1))
      = (∑ i ∈ Finset.range 9, stT139 (i+1)) + stT139 10 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 9
    simpa using h
  have hprev := st139_p9
  have hstep := st139_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p11 : ((8502246341/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT139 (i+1))
      = (∑ i ∈ Finset.range 10, stT139 (i+1)) + stT139 11 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 10
    simpa using h
  have hprev := st139_p10
  have hstep := st139_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p12 : ((1185483915437/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT139 (i+1))
      = (∑ i ∈ Finset.range 11, stT139 (i+1)) + stT139 12 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 11
    simpa using h
  have hprev := st139_p11
  have hstep := st139_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p13 : ((3818943099963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT139 (i+1))
      = (∑ i ∈ Finset.range 12, stT139 (i+1)) + stT139 13 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 12
    simpa using h
  have hprev := st139_p12
  have hstep := st139_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p14 : ((756996975837/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT139 (i+1))
      = (∑ i ∈ Finset.range 13, stT139 (i+1)) + stT139 14 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 13
    simpa using h
  have hprev := st139_p13
  have hstep := st139_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p15 : ((169670058653/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT139 (i+1))
      = (∑ i ∈ Finset.range 14, stT139 (i+1)) + stT139 15 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 14
    simpa using h
  have hprev := st139_p14
  have hstep := st139_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p16 : ((196919358653/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT139 (i+1))
      = (∑ i ∈ Finset.range 15, stT139 (i+1)) + stT139 16 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 15
    simpa using h
  have hprev := st139_p15
  have hstep := st139_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p17 : ((2603552007943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT139 (i+1))
      = (∑ i ∈ Finset.range 16, stT139 (i+1)) + stT139 17 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 16
    simpa using h
  have hprev := st139_p16
  have hstep := st139_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p18 : ((3494833950001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT139 (i+1))
      = (∑ i ∈ Finset.range 17, stT139 (i+1)) + stT139 18 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 17
    simpa using h
  have hprev := st139_p17
  have hstep := st139_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p19 : ((5786100312181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT139 (i+1))
      = (∑ i ∈ Finset.range 18, stT139 (i+1)) + stT139 19 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 18
    simpa using h
  have hprev := st139_p18
  have hstep := st139_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p20 : ((3591663450867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT139 (i+1))
      = (∑ i ∈ Finset.range 19, stT139 (i+1)) + stT139 20 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 19
    simpa using h
  have hprev := st139_p19
  have hstep := st139_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p21 : ((1891519685189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT139 (i+1))
      = (∑ i ∈ Finset.range 20, stT139 (i+1)) + stT139 21 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 20
    simpa using h
  have hprev := st139_p20
  have hstep := st139_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p22 : ((604129557/800000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT139 (i+1))
      = (∑ i ∈ Finset.range 21, stT139 (i+1)) + stT139 22 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 21
    simpa using h
  have hprev := st139_p21
  have hstep := st139_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p23 : ((1938703143753/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT139 (i+1))
      = (∑ i ∈ Finset.range 22, stT139 (i+1)) + stT139 23 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 22
    simpa using h
  have hprev := st139_p22
  have hstep := st139_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p24 : ((8670147905473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT139 (i+1))
      = (∑ i ∈ Finset.range 23, stT139 (i+1)) + stT139 24 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 23
    simpa using h
  have hprev := st139_p23
  have hstep := st139_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p25 : ((10428257905473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT139 (i+1))
      = (∑ i ∈ Finset.range 24, stT139 (i+1)) + stT139 25 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 24
    simpa using h
  have hprev := st139_p24
  have hstep := st139_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p26 : ((6140248992347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT139 (i+1))
      = (∑ i ∈ Finset.range 25, stT139 (i+1)) + stT139 26 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 25
    simpa using h
  have hprev := st139_p25
  have hstep := st139_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p27 : ((6330257764097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT139 (i+1))
      = (∑ i ∈ Finset.range 26, stT139 (i+1)) + stT139 27 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 26
    simpa using h
  have hprev := st139_p26
  have hstep := st139_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p28 : ((11041003360999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT139 (i+1))
      = (∑ i ∈ Finset.range 27, stT139 (i+1)) + stT139 28 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 27
    simpa using h
  have hprev := st139_p27
  have hstep := st139_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p29 : ((9834935878401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT139 (i+1))
      = (∑ i ∈ Finset.range 28, stT139 (i+1)) + stT139 29 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 28
    simpa using h
  have hprev := st139_p28
  have hstep := st139_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p30 : ((11223262198139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT139 (i+1))
      = (∑ i ∈ Finset.range 29, stT139 (i+1)) + stT139 30 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 29
    simpa using h
  have hprev := st139_p29
  have hstep := st139_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p31 : ((12165266851897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT139 (i+1))
      = (∑ i ∈ Finset.range 30, stT139 (i+1)) + stT139 31 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 30
    simpa using h
  have hprev := st139_p30
  have hstep := st139_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p32 : ((5226810575423/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT139 (i+1))
      = (∑ i ∈ Finset.range 31, stT139 (i+1)) + stT139 32 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 31
    simpa using h
  have hprev := st139_p31
  have hstep := st139_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p33 : ((215382004891/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT139 (i+1))
      = (∑ i ∈ Finset.range 32, stT139 (i+1)) + stT139 33 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 32
    simpa using h
  have hprev := st139_p32
  have hstep := st139_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p34 : ((1202955248009/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT139 (i+1))
      = (∑ i ∈ Finset.range 33, stT139 (i+1)) + stT139 34 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 33
    simpa using h
  have hprev := st139_p33
  have hstep := st139_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p35 : ((2071261429889/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT139 (i+1))
      = (∑ i ∈ Finset.range 34, stT139 (i+1)) + stT139 35 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 34
    simpa using h
  have hprev := st139_p34
  have hstep := st139_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p36 : ((11370263410529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT139 (i+1))
      = (∑ i ∈ Finset.range 35, stT139 (i+1)) + stT139 36 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 35
    simpa using h
  have hprev := st139_p35
  have hstep := st139_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p37 : ((11391217694323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT139 (i+1))
      = (∑ i ∈ Finset.range 36, stT139 (i+1)) + stT139 37 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 36
    simpa using h
  have hprev := st139_p36
  have hstep := st139_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p38 : ((656545467843/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT139 (i+1))
      = (∑ i ∈ Finset.range 37, stT139 (i+1)) + stT139 38 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 37
    simpa using h
  have hprev := st139_p37
  have hstep := st139_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p39 : ((11891307127727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT139 (i+1))
      = (∑ i ∈ Finset.range 38, stT139 (i+1)) + stT139 39 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 38
    simpa using h
  have hprev := st139_p38
  have hstep := st139_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p40 : ((10326940850239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT139 (i+1))
      = (∑ i ∈ Finset.range 39, stT139 (i+1)) + stT139 40 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 39
    simpa using h
  have hprev := st139_p39
  have hstep := st139_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p41 : ((1484039051027/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT139 (i+1))
      = (∑ i ∈ Finset.range 40, stT139 (i+1)) + stT139 41 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 40
    simpa using h
  have hprev := st139_p40
  have hstep := st139_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p42 : ((5212045066173/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT139 (i+1))
      = (∑ i ∈ Finset.range 41, stT139 (i+1)) + stT139 42 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 41
    simpa using h
  have hprev := st139_p41
  have hstep := st139_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p43 : ((11775490664751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT139 (i+1))
      = (∑ i ∈ Finset.range 42, stT139 (i+1)) + stT139 43 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 42
    simpa using h
  have hprev := st139_p42
  have hstep := st139_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p44 : ((10478985614523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT139 (i+1))
      = (∑ i ∈ Finset.range 43, stT139 (i+1)) + stT139 44 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 43
    simpa using h
  have hprev := st139_p43
  have hstep := st139_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p45 : ((11774246513891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT139 (i+1))
      = (∑ i ∈ Finset.range 44, stT139 (i+1)) + stT139 45 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 44
    simpa using h
  have hprev := st139_p44
  have hstep := st139_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p46 : ((10434725622951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT139 (i+1))
      = (∑ i ∈ Finset.range 45, stT139 (i+1)) + stT139 46 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 45
    simpa using h
  have hprev := st139_p45
  have hstep := st139_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p47 : ((18495151863/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT139 (i+1))
      = (∑ i ∈ Finset.range 46, stT139 (i+1)) + stT139 47 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 46
    simpa using h
  have hprev := st139_p46
  have hstep := st139_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p48 : ((649774323777/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT139 (i+1))
      = (∑ i ∈ Finset.range 47, stT139 (i+1)) + stT139 48 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 47
    simpa using h
  have hprev := st139_p47
  have hstep := st139_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p49 : ((11792998761449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT139 (i+1))
      = (∑ i ∈ Finset.range 48, stT139 (i+1)) + stT139 49 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 48
    simpa using h
  have hprev := st139_p48
  have hstep := st139_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p50 : ((10583666186271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT139 (i+1))
      = (∑ i ∈ Finset.range 49, stT139 (i+1)) + stT139 50 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 49
    simpa using h
  have hprev := st139_p49
  have hstep := st139_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p51 : ((11416090637871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT139 (i+1))
      = (∑ i ∈ Finset.range 50, stT139 (i+1)) + stT139 51 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 50
    simpa using h
  have hprev := st139_p50
  have hstep := st139_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p52 : ((11148414412847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT139 (i+1))
      = (∑ i ∈ Finset.range 51, stT139 (i+1)) + stT139 52 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 51
    simpa using h
  have hprev := st139_p51
  have hstep := st139_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p53 : ((10742810538743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT139 (i+1))
      = (∑ i ∈ Finset.range 52, stT139 (i+1)) + stT139 53 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 52
    simpa using h
  have hprev := st139_p52
  have hstep := st139_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p54 : ((5879438050387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT139 (i+1))
      = (∑ i ∈ Finset.range 53, stT139 (i+1)) + stT139 54 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 53
    simpa using h
  have hprev := st139_p53
  have hstep := st139_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p55 : ((5211487884387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT139 (i+1))
      = (∑ i ∈ Finset.range 54, stT139 (i+1)) + stT139 55 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 54
    simpa using h
  have hprev := st139_p54
  have hstep := st139_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p56 : ((5797690582631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT139 (i+1))
      = (∑ i ∈ Finset.range 55, stT139 (i+1)) + stT139 56 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 55
    simpa using h
  have hprev := st139_p55
  have hstep := st139_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p57 : ((11092889107453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT139 (i+1))
      = (∑ i ∈ Finset.range 56, stT139 (i+1)) + stT139 57 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 56
    simpa using h
  have hprev := st139_p56
  have hstep := st139_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p58 : ((10661043037993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT139 (i+1))
      = (∑ i ∈ Finset.range 57, stT139 (i+1)) + stT139 58 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 57
    simpa using h
  have hprev := st139_p57
  have hstep := st139_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p59 : ((11821549496371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT139 (i+1))
      = (∑ i ∈ Finset.range 58, stT139 (i+1)) + stT139 59 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 58
    simpa using h
  have hprev := st139_p58
  have hstep := st139_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p60 : ((5301159808713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT139 (i+1))
      = (∑ i ∈ Finset.range 59, stT139 (i+1)) + stT139 60 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 59
    simpa using h
  have hprev := st139_p59
  have hstep := st139_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p61 : ((221819262041/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT139 (i+1))
      = (∑ i ∈ Finset.range 60, stT139 (i+1)) + stT139 61 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 60
    simpa using h
  have hprev := st139_p60
  have hstep := st139_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p62 : ((1168832077241/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT139 (i+1))
      = (∑ i ∈ Finset.range 61, stT139 (i+1)) + stT139 62 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 61
    simpa using h
  have hprev := st139_p61
  have hstep := st139_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p63 : ((326411838267/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT139 (i+1))
      = (∑ i ∈ Finset.range 62, stT139 (i+1)) + stT139 63 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 62
    simpa using h
  have hprev := st139_p62
  have hstep := st139_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p64 : ((353929494517/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT139 (i+1))
      = (∑ i ∈ Finset.range 63, stT139 (i+1)) + stT139 64 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 63
    simpa using h
  have hprev := st139_p63
  have hstep := st139_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p65 : ((5788959386557/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT139 (i+1))
      = (∑ i ∈ Finset.range 64, stT139 (i+1)) + stT139 65 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 64
    simpa using h
  have hprev := st139_p64
  have hstep := st139_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p66 : ((5210069909377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT139 (i+1))
      = (∑ i ∈ Finset.range 65, stT139 (i+1)) + stT139 66 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 65
    simpa using h
  have hprev := st139_p65
  have hstep := st139_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p67 : ((567537589231/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT139 (i+1))
      = (∑ i ∈ Finset.range 66, stT139 (i+1)) + stT139 67 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 66
    simpa using h
  have hprev := st139_p66
  have hstep := st139_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p68 : ((5805431363437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT139 (i+1))
      = (∑ i ∈ Finset.range 67, stT139 (i+1)) + stT139 68 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 67
    simpa using h
  have hprev := st139_p67
  have hstep := st139_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p69 : ((5221042089067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT139 (i+1))
      = (∑ i ∈ Finset.range 68, stT139 (i+1)) + stT139 69 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 68
    simpa using h
  have hprev := st139_p68
  have hstep := st139_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p70 : ((5592799232433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT139 (i+1))
      = (∑ i ∈ Finset.range 69, stT139 (i+1)) + stT139 70 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 69
    simpa using h
  have hprev := st139_p69
  have hstep := st139_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p71 : ((11752935561573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT139 (i+1))
      = (∑ i ∈ Finset.range 70, stT139 (i+1)) + stT139 71 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 70
    simpa using h
  have hprev := st139_p70
  have hstep := st139_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p72 : ((2116717534177/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT139 (i+1))
      = (∑ i ∈ Finset.range 71, stT139 (i+1)) + stT139 72 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 71
    simpa using h
  have hprev := st139_p71
  have hstep := st139_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p73 : ((1355051808481/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT139 (i+1))
      = (∑ i ∈ Finset.range 72, stT139 (i+1)) + stT139 73 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 72
    simpa using h
  have hprev := st139_p72
  have hstep := st139_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p74 : ((2959106266781/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT139 (i+1))
      = (∑ i ∈ Finset.range 73, stT139 (i+1)) + stT139 74 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 73
    simpa using h
  have hprev := st139_p73
  have hstep := st139_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p75 : ((219581791937/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT139 (i+1))
      = (∑ i ∈ Finset.range 74, stT139 (i+1)) + stT139 75 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 74
    simpa using h
  have hprev := st139_p74
  have hstep := st139_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p76 : ((418634311011/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT139 (i+1))
      = (∑ i ∈ Finset.range 75, stT139 (i+1)) + stT139 76 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 75
    simpa using h
  have hprev := st139_p75
  have hstep := st139_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p77 : ((2315706325983/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT139 (i+1))
      = (∑ i ∈ Finset.range 76, stT139 (i+1)) + stT139 77 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 76
    simpa using h
  have hprev := st139_p76
  have hstep := st139_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p78 : ((11572617741921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT139 (i+1))
      = (∑ i ∈ Finset.range 77, stT139 (i+1)) + stT139 78 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 77
    simpa using h
  have hprev := st139_p77
  have hstep := st139_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p79 : ((10471054206913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT139 (i+1))
      = (∑ i ∈ Finset.range 78, stT139 (i+1)) + stT139 79 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 78
    simpa using h
  have hprev := st139_p78
  have hstep := st139_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p80 : ((2722139479001/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT139 (i+1))
      = (∑ i ∈ Finset.range 79, stT139 (i+1)) + stT139 80 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 79
    simpa using h
  have hprev := st139_p79
  have hstep := st139_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p81 : ((5921131132539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT139 (i+1))
      = (∑ i ∈ Finset.range 80, stT139 (i+1)) + stT139 81 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 80
    simpa using h
  have hprev := st139_p80
  have hstep := st139_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p82 : ((5576736936147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT139 (i+1))
      = (∑ i ∈ Finset.range 81, stT139 (i+1)) + stT139 82 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 81
    simpa using h
  have hprev := st139_p81
  have hstep := st139_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p83 : ((10378910015271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT139 (i+1))
      = (∑ i ∈ Finset.range 82, stT139 (i+1)) + stT139 83 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 82
    simpa using h
  have hprev := st139_p82
  have hstep := st139_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p84 : ((11220772465891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT139 (i+1))
      = (∑ i ∈ Finset.range 83, stT139 (i+1)) + stT139 84 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 83
    simpa using h
  have hprev := st139_p83
  have hstep := st139_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p85 : ((11846698018791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT139 (i+1))
      = (∑ i ∈ Finset.range 84, stT139 (i+1)) + stT139 85 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 84
    simpa using h
  have hprev := st139_p84
  have hstep := st139_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p86 : ((10933171965359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT139 (i+1))
      = (∑ i ∈ Finset.range 85, stT139 (i+1)) + stT139 86 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 85
    simpa using h
  have hprev := st139_p85
  have hstep := st139_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p87 : ((1039660835591/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT139 (i+1))
      = (∑ i ∈ Finset.range 86, stT139 (i+1)) + stT139 87 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 86
    simpa using h
  have hprev := st139_p86
  have hstep := st139_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p88 : ((2832206461851/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT139 (i+1))
      = (∑ i ∈ Finset.range 87, stT139 (i+1)) + stT139 88 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 87
    simpa using h
  have hprev := st139_p87
  have hstep := st139_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p89 : ((11842961492299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT139 (i+1))
      = (∑ i ∈ Finset.range 88, stT139 (i+1)) + stT139 89 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 88
    simpa using h
  have hprev := st139_p88
  have hstep := st139_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p90 : ((1366292157467/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT139 (i+1))
      = (∑ i ∈ Finset.range 89, stT139 (i+1)) + stT139 90 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 89
    simpa using h
  have hprev := st139_p89
  have hstep := st139_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p91 : ((5187154013303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT139 (i+1))
      = (∑ i ∈ Finset.range 90, stT139 (i+1)) + stT139 91 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 90
    simpa using h
  have hprev := st139_p90
  have hstep := st139_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p92 : ((5614192025789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT139 (i+1))
      = (∑ i ∈ Finset.range 91, stT139 (i+1)) + stT139 92 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 91
    simpa using h
  have hprev := st139_p91
  have hstep := st139_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p93 : ((2969842879967/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT139 (i+1))
      = (∑ i ∈ Finset.range 92, stT139 (i+1)) + stT139 93 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 92
    simpa using h
  have hprev := st139_p92
  have hstep := st139_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p94 : ((2783447390393/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT139 (i+1))
      = (∑ i ∈ Finset.range 93, stT139 (i+1)) + stT139 94 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 93
    simpa using h
  have hprev := st139_p93
  have hstep := st139_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p95 : ((5177165371867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT139 (i+1))
      = (∑ i ∈ Finset.range 94, stT139 (i+1)) + stT139 95 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 94
    simpa using h
  have hprev := st139_p94
  have hstep := st139_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p96 : ((5462201063607/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT139 (i+1))
      = (∑ i ∈ Finset.range 95, stT139 (i+1)) + stT139 96 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 95
    simpa using h
  have hprev := st139_p95
  have hstep := st139_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p97 : ((2958274807353/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT139 (i+1))
      = (∑ i ∈ Finset.range 96, stT139 (i+1)) + stT139 97 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 96
    simpa using h
  have hprev := st139_p96
  have hstep := st139_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p98 : ((5758991000531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT139 (i+1))
      = (∑ i ∈ Finset.range 97, stT139 (i+1)) + stT139 98 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 97
    simpa using h
  have hprev := st139_p97
  have hstep := st139_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p99 : ((5262673084991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT139 (i+1))
      = (∑ i ∈ Finset.range 98, stT139 (i+1)) + stT139 99 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 98
    simpa using h
  have hprev := st139_p98
  have hstep := st139_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p100 : ((5254535584991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT139 (i+1))
      = (∑ i ∈ Finset.range 99, stT139 (i+1)) + stT139 100 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 99
    simpa using h
  have hprev := st139_p99
  have hstep := st139_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p101 : ((11483442246529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT139 (i+1))
      = (∑ i ∈ Finset.range 100, stT139 (i+1)) + stT139 101 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 100
    simpa using h
  have hprev := st139_p100
  have hstep := st139_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p102 : ((5936874641303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT139 (i+1))
      = (∑ i ∈ Finset.range 101, stT139 (i+1)) + stT139 102 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 101
    simpa using h
  have hprev := st139_p101
  have hstep := st139_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p103 : ((1383965889977/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT139 (i+1))
      = (∑ i ∈ Finset.range 102, stT139 (i+1)) + stT139 103 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 102
    simpa using h
  have hprev := st139_p102
  have hstep := st139_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p104 : ((323014253357/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT139 (i+1))
      = (∑ i ∈ Finset.range 103, stT139 (i+1)) + stT139 104 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 103
    simpa using h
  have hprev := st139_p103
  have hstep := st139_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p105 : ((2697289393831/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT139 (i+1))
      = (∑ i ∈ Finset.range 104, stT139 (i+1)) + stT139 105 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 104
    simpa using h
  have hprev := st139_p104
  have hstep := st139_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p106 : ((11734999764749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT139 (i+1))
      = (∑ i ∈ Finset.range 105, stT139 (i+1)) + stT139 106 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 105
    simpa using h
  have hprev := st139_p105
  have hstep := st139_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p107 : ((2354035084169/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT139 (i+1))
      = (∑ i ∈ Finset.range 106, stT139 (i+1)) + stT139 107 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 106
    simpa using h
  have hprev := st139_p106
  have hstep := st139_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p108 : ((10854986192753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT139 (i+1))
      = (∑ i ∈ Finset.range 107, stT139 (i+1)) + stT139 108 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 107
    simpa using h
  have hprev := st139_p107
  have hstep := st139_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p109 : ((2577758341493/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT139 (i+1))
      = (∑ i ∈ Finset.range 108, stT139 (i+1)) + stT139 109 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 108
    simpa using h
  have hprev := st139_p108
  have hstep := st139_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p110 : ((2724929968503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT139 (i+1))
      = (∑ i ∈ Finset.range 109, stT139 (i+1)) + stT139 110 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 109
    simpa using h
  have hprev := st139_p109
  have hstep := st139_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p111 : ((11790415446911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT139 (i+1))
      = (∑ i ∈ Finset.range 110, stT139 (i+1)) + stT139 111 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 110
    simpa using h
  have hprev := st139_p110
  have hstep := st139_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p112 : ((11763441044047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT139 (i+1))
      = (∑ i ∈ Finset.range 111, stT139 (i+1)) + stT139 112 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 111
    simpa using h
  have hprev := st139_p111
  have hstep := st139_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p113 : ((10866578338509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT139 (i+1))
      = (∑ i ∈ Finset.range 112, stT139 (i+1)) + stT139 113 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 112
    simpa using h
  have hprev := st139_p112
  have hstep := st139_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p114 : ((10297601406923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT139 (i+1))
      = (∑ i ∈ Finset.range 113, stT139 (i+1)) + stT139 114 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 113
    simpa using h
  have hprev := st139_p113
  have hstep := st139_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p115 : ((10793785852819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT139 (i+1))
      = (∑ i ∈ Finset.range 114, stT139 (i+1)) + stT139 115 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 114
    simpa using h
  have hprev := st139_p114
  have hstep := st139_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p116 : ((11704833429823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT139 (i+1))
      = (∑ i ∈ Finset.range 115, stT139 (i+1)) + stT139 116 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 115
    simpa using h
  have hprev := st139_p115
  have hstep := st139_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p117 : ((11873796898823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT139 (i+1))
      = (∑ i ∈ Finset.range 116, stT139 (i+1)) + stT139 117 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 116
    simpa using h
  have hprev := st139_p116
  have hstep := st139_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p118 : ((1387442606381/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT139 (i+1))
      = (∑ i ∈ Finset.range 117, stT139 (i+1)) + stT139 118 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 117
    simpa using h
  have hprev := st139_p117
  have hstep := st139_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p119 : ((10343604271377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT139 (i+1))
      = (∑ i ∈ Finset.range 118, stT139 (i+1)) + stT139 119 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 118
    simpa using h
  have hprev := st139_p118
  have hstep := st139_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p120 : ((10519309837497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT139 (i+1))
      = (∑ i ∈ Finset.range 119, stT139 (i+1)) + stT139 120 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 119
    simpa using h
  have hprev := st139_p119
  have hstep := st139_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p121 : ((11405738041977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT139 (i+1))
      = (∑ i ∈ Finset.range 120, stT139 (i+1)) + stT139 121 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 120
    simpa using h
  have hprev := st139_p120
  have hstep := st139_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p122 : ((11953806766211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT139 (i+1))
      = (∑ i ∈ Finset.range 121, stT139 (i+1)) + stT139 122 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 121
    simpa using h
  have hprev := st139_p121
  have hstep := st139_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p123 : ((11533862078741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT139 (i+1))
      = (∑ i ∈ Finset.range 122, stT139 (i+1)) + stT139 123 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 122
    simpa using h
  have hprev := st139_p122
  have hstep := st139_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p124 : ((5318238584023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT139 (i+1))
      = (∑ i ∈ Finset.range 123, stT139 (i+1)) + stT139 124 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 123
    simpa using h
  have hprev := st139_p123
  have hstep := st139_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p125 : ((5137825748213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT139 (i+1))
      = (∑ i ∈ Finset.range 124, stT139 (i+1)) + stT139 125 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 124
    simpa using h
  have hprev := st139_p124
  have hstep := st139_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p126 : ((2711079467729/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT139 (i+1))
      = (∑ i ∈ Finset.range 125, stT139 (i+1)) + stT139 126 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 125
    simpa using h
  have hprev := st139_p125
  have hstep := st139_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p127 : ((2927541090369/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT139 (i+1))
      = (∑ i ∈ Finset.range 126, stT139 (i+1)) + stT139 127 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 126
    simpa using h
  have hprev := st139_p126
  have hstep := st139_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p128 : ((5968755721719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT139 (i+1))
      = (∑ i ∈ Finset.range 127, stT139 (i+1)) + stT139 128 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 127
    simpa using h
  have hprev := st139_p127
  have hstep := st139_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p129 : ((1411601030287/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT139 (i+1))
      = (∑ i ∈ Finset.range 128, stT139 (i+1)) + stT139 129 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 128
    simpa using h
  have hprev := st139_p128
  have hstep := st139_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p130 : ((2092273191589/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT139 (i+1))
      = (∑ i ∈ Finset.range 129, stT139 (i+1)) + stT139 130 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 129
    simpa using h
  have hprev := st139_p129
  have hstep := st139_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p131 : ((2060713219579/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT139 (i+1))
      = (∑ i ∈ Finset.range 130, stT139 (i+1)) + stT139 131 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 130
    simpa using h
  have hprev := st139_p130
  have hstep := st139_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p132 : ((10971852615459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT139 (i+1))
      = (∑ i ∈ Finset.range 131, stT139 (i+1)) + stT139 132 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 131
    simpa using h
  have hprev := st139_p131
  have hstep := st139_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p133 : ((5892613868919/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT139 (i+1))
      = (∑ i ∈ Finset.range 132, stT139 (i+1)) + stT139 133 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 132
    simpa using h
  have hprev := st139_p132
  have hstep := st139_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p134 : ((5968156101981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT139 (i+1))
      = (∑ i ∈ Finset.range 133, stT139 (i+1)) + stT139 134 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 133
    simpa using h
  have hprev := st139_p133
  have hstep := st139_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p135 : ((11285366096509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT139 (i+1))
      = (∑ i ∈ Finset.range 134, stT139 (i+1)) + stT139 135 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 134
    simpa using h
  have hprev := st139_p134
  have hstep := st139_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p136 : ((523469945501/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT139 (i+1))
      = (∑ i ∈ Finset.range 135, stT139 (i+1)) + stT139 136 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 135
    simpa using h
  have hprev := st139_p135
  have hstep := st139_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p137 : ((5133210695369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT139 (i+1))
      = (∑ i ∈ Finset.range 136, stT139 (i+1)) + stT139 137 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 136
    simpa using h
  have hprev := st139_p136
  have hstep := st139_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p138 : ((5429815100333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT139 (i+1))
      = (∑ i ∈ Finset.range 137, stT139 (i+1)) + stT139 138 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 137
    simpa using h
  have hprev := st139_p137
  have hstep := st139_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p139 : ((5845101516141/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT139 (i+1))
      = (∑ i ∈ Finset.range 138, stT139 (i+1)) + stT139 139 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 138
    simpa using h
  have hprev := st139_p138
  have hstep := st139_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p140 : ((1499518491891/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT139 (i+1))
      = (∑ i ∈ Finset.range 139, stT139 (i+1)) + stT139 140 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 139
    simpa using h
  have hprev := st139_p139
  have hstep := st139_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p141 : ((89902911017/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT139 (i+1))
      = (∑ i ∈ Finset.range 140, stT139 (i+1)) + stT139 141 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 140
    simpa using h
  have hprev := st139_p140
  have hstep := st139_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p142 : ((266718408829/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT139 (i+1))
      = (∑ i ∈ Finset.range 141, stT139 (i+1)) + stT139 142 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 141
    simpa using h
  have hprev := st139_p141
  have hstep := st139_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p143 : ((2044198188977/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT139 (i+1))
      = (∑ i ∈ Finset.range 142, stT139 (i+1)) + stT139 143 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 142
    simpa using h
  have hprev := st139_p142
  have hstep := st139_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p144 : ((10548289147299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT139 (i+1))
      = (∑ i ∈ Finset.range 143, stT139 (i+1)) + stT139 144 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 143
    simpa using h
  have hprev := st139_p143
  have hstep := st139_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p145 : ((11361285343311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT139 (i+1))
      = (∑ i ∈ Finset.range 144, stT139 (i+1)) + stT139 145 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 144
    simpa using h
  have hprev := st139_p144
  have hstep := st139_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p146 : ((5983348717863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT139 (i+1))
      = (∑ i ∈ Finset.range 145, stT139 (i+1)) + stT139 146 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 145
    simpa using h
  have hprev := st139_p145
  have hstep := st139_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p147 : ((474449177907/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT139 (i+1))
      = (∑ i ∈ Finset.range 146, stT139 (i+1)) + stT139 147 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 146
    simpa using h
  have hprev := st139_p146
  have hstep := st139_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p148 : ((44559666021/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT139 (i+1))
      = (∑ i ∈ Finset.range 147, stT139 (i+1)) + stT139 148 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 147
    simpa using h
  have hprev := st139_p147
  have hstep := st139_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p149 : ((1039721306253/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT139 (i+1))
      = (∑ i ∈ Finset.range 148, stT139 (i+1)) + stT139 149 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 148
    simpa using h
  have hprev := st139_p148
  have hstep := st139_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p150 : ((5115382625049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT139 (i+1))
      = (∑ i ∈ Finset.range 149, stT139 (i+1)) + stT139 150 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 149
    simpa using h
  have hprev := st139_p149
  have hstep := st139_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p151 : ((5383158345767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT139 (i+1))
      = (∑ i ∈ Finset.range 150, stT139 (i+1)) + stT139 151 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 150
    simpa using h
  have hprev := st139_p150
  have hstep := st139_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p152 : ((11575667644879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT139 (i+1))
      = (∑ i ∈ Finset.range 151, stT139 (i+1)) + stT139 152 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 151
    simpa using h
  have hprev := st139_p151
  have hstep := st139_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p153 : ((12028277071723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT139 (i+1))
      = (∑ i ∈ Finset.range 152, stT139 (i+1)) + stT139 153 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 152
    simpa using h
  have hprev := st139_p152
  have hstep := st139_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p154 : ((2945357529489/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT139 (i+1))
      = (∑ i ∈ Finset.range 153, stT139 (i+1)) + stT139 154 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 153
    simpa using h
  have hprev := st139_p153
  have hstep := st139_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p155 : ((2757403246269/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT139 (i+1))
      = (∑ i ∈ Finset.range 154, stT139 (i+1)) + stT139 155 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 154
    simpa using h
  have hprev := st139_p154
  have hstep := st139_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p156 : ((5170211406779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT139 (i+1))
      = (∑ i ∈ Finset.range 155, stT139 (i+1)) + stT139 156 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 155
    simpa using h
  have hprev := st139_p155
  have hstep := st139_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p157 : ((5111129026169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT139 (i+1))
      = (∑ i ∈ Finset.range 156, stT139 (i+1)) + stT139 157 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 156
    simpa using h
  have hprev := st139_p156
  have hstep := st139_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p158 : ((336097119091/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT139 (i+1))
      = (∑ i ∈ Finset.range 157, stT139 (i+1)) + stT139 158 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 157
    simpa using h
  have hprev := st139_p157
  have hstep := st139_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p159 : ((2309495833241/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT139 (i+1))
      = (∑ i ∈ Finset.range 158, stT139 (i+1)) + stT139 159 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 158
    simpa using h
  have hprev := st139_p158
  have hstep := st139_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p160 : ((2406324724361/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT139 (i+1))
      = (∑ i ∈ Finset.range 159, stT139 (i+1)) + stT139 160 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 159
    simpa using h
  have hprev := st139_p159
  have hstep := st139_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p161 : ((2373939667149/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT139 (i+1))
      = (∑ i ∈ Finset.range 160, stT139 (i+1)) + stT139 161 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 160
    simpa using h
  have hprev := st139_p160
  have hstep := st139_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p162 : ((2236276522079/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT139 (i+1))
      = (∑ i ∈ Finset.range 161, stT139 (i+1)) + stT139 162 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 161
    simpa using h
  have hprev := st139_p161
  have hstep := st139_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p163 : ((10446152741437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT139 (i+1))
      = (∑ i ∈ Finset.range 162, stT139 (i+1)) + stT139 163 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 162
    simpa using h
  have hprev := st139_p162
  have hstep := st139_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p164 : ((10164847807663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT139 (i+1))
      = (∑ i ∈ Finset.range 163, stT139 (i+1)) + stT139 164 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 163
    simpa using h
  have hprev := st139_p163
  have hstep := st139_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p165 : ((10521886452913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT139 (i+1))
      = (∑ i ∈ Finset.range 164, stT139 (i+1)) + stT139 165 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 164
    simpa using h
  have hprev := st139_p164
  have hstep := st139_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p166 : ((11273014153063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT139 (i+1))
      = (∑ i ∈ Finset.range 165, stT139 (i+1)) + stT139 166 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 165
    simpa using h
  have hprev := st139_p165
  have hstep := st139_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p167 : ((1490008200011/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT139 (i+1))
      = (∑ i ∈ Finset.range 166, stT139 (i+1)) + stT139 167 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 166
    simpa using h
  have hprev := st139_p166
  have hstep := st139_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p168 : ((3010834413763/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT139 (i+1))
      = (∑ i ∈ Finset.range 167, stT139 (i+1)) + stT139 168 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 167
    simpa using h
  have hprev := st139_p167
  have hstep := st139_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p169 : ((289224745511/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT139 (i+1))
      = (∑ i ∈ Finset.range 168, stT139 (i+1)) + stT139 169 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 168
    simpa using h
  have hprev := st139_p168
  have hstep := st139_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p170 : ((2160968376577/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT139 (i+1))
      = (∑ i ∈ Finset.range 169, stT139 (i+1)) + stT139 170 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 169
    simpa using h
  have hprev := st139_p169
  have hstep := st139_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p171 : ((2046881788049/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT139 (i+1))
      = (∑ i ∈ Finset.range 170, stT139 (i+1)) + stT139 171 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 170
    simpa using h
  have hprev := st139_p170
  have hstep := st139_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p172 : ((10210454460157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT139 (i+1))
      = (∑ i ∈ Finset.range 171, stT139 (i+1)) + stT139 172 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 171
    simpa using h
  have hprev := st139_p171
  have hstep := st139_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p173 : ((10742088308117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT139 (i+1))
      = (∑ i ∈ Finset.range 172, stT139 (i+1)) + stT139 173 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 172
    simpa using h
  have hprev := st139_p172
  have hstep := st139_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p174 : ((11500140064139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT139 (i+1))
      = (∑ i ∈ Finset.range 173, stT139 (i+1)) + stT139 174 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 173
    simpa using h
  have hprev := st139_p173
  have hstep := st139_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p175 : ((481041173867/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT139 (i+1))
      = (∑ i ∈ Finset.range 174, stT139 (i+1)) + stT139 175 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 174
    simpa using h
  have hprev := st139_p174
  have hstep := st139_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p176 : ((15011218871/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT139 (i+1))
      = (∑ i ∈ Finset.range 175, stT139 (i+1)) + stT139 176 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 175
    simpa using h
  have hprev := st139_p175
  have hstep := st139_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p177 : ((5732232736883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT139 (i+1))
      = (∑ i ∈ Finset.range 176, stT139 (i+1)) + stT139 177 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 176
    simpa using h
  have hprev := st139_p176
  have hstep := st139_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p178 : ((5357542064849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT139 (i+1))
      = (∑ i ∈ Finset.range 177, stT139 (i+1)) + stT139 178 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 177
    simpa using h
  have hprev := st139_p177
  have hstep := st139_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p179 : ((5097458628519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT139 (i+1))
      = (∑ i ∈ Finset.range 178, stT139 (i+1)) + stT139 179 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 178
    simpa using h
  have hprev := st139_p178
  have hstep := st139_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p180 : ((10198395828823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT139 (i+1))
      = (∑ i ∈ Finset.range 179, stT139 (i+1)) + stT139 180 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 179
    simpa using h
  have hprev := st139_p179
  have hstep := st139_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p181 : ((10718350050761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT139 (i+1))
      = (∑ i ∈ Finset.range 180, stT139 (i+1)) + stT139 181 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 180
    simpa using h
  have hprev := st139_p180
  have hstep := st139_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p182 : ((716201545001/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT139 (i+1))
      = (∑ i ∈ Finset.range 181, stT139 (i+1)) + stT139 182 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 181
    simpa using h
  have hprev := st139_p181
  have hstep := st139_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p183 : ((750581235269/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT139 (i+1))
      = (∑ i ∈ Finset.range 182, stT139 (i+1)) + stT139 183 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 182
    simpa using h
  have hprev := st139_p182
  have hstep := st139_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p184 : ((12069505411707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT139 (i+1))
      = (∑ i ∈ Finset.range 183, stT139 (i+1)) + stT139 184 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 183
    simpa using h
  have hprev := st139_p183
  have hstep := st139_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p185 : ((11611997291937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT139 (i+1))
      = (∑ i ∈ Finset.range 184, stT139 (i+1)) + stT139 185 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 184
    simpa using h
  have hprev := st139_p184
  have hstep := st139_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p186 : ((10886945672169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT139 (i+1))
      = (∑ i ∈ Finset.range 185, stT139 (i+1)) + stT139 186 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 185
    simpa using h
  have hprev := st139_p185
  have hstep := st139_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p187 : ((2056296468327/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT139 (i+1))
      = (∑ i ∈ Finset.range 186, stT139 (i+1)) + stT139 187 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 186
    simpa using h
  have hprev := st139_p186
  have hstep := st139_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p188 : ((252807721099/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT139 (i+1))
      = (∑ i ∈ Finset.range 187, stT139 (i+1)) + stT139 188 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 187
    simpa using h
  have hprev := st139_p187
  have hstep := st139_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p189 : ((261578795683/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT139 (i+1))
      = (∑ i ∈ Finset.range 188, stT139 (i+1)) + stT139 189 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 188
    simpa using h
  have hprev := st139_p188
  have hstep := st139_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p190 : ((348391223787/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT139 (i+1))
      = (∑ i ∈ Finset.range 189, stT139 (i+1)) + stT139 190 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 189
    simpa using h
  have hprev := st139_p189
  have hstep := st139_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p191 : ((1477016493503/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT139 (i+1))
      = (∑ i ∈ Finset.range 190, stT139 (i+1)) + stT139 191 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 190
    simpa using h
  have hprev := st139_p190
  have hstep := st139_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p192 : ((2425898121697/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT139 (i+1))
      = (∑ i ∈ Finset.range 191, stT139 (i+1)) + stT139 192 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 191
    simpa using h
  have hprev := st139_p191
  have hstep := st139_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p193 : ((2387093560953/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT139 (i+1))
      = (∑ i ∈ Finset.range 192, stT139 (i+1)) + stT139 193 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 192
    simpa using h
  have hprev := st139_p192
  have hstep := st139_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p194 : ((1133471920131/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT139 (i+1))
      = (∑ i ∈ Finset.range 193, stT139 (i+1)) + stT139 194 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 193
    simpa using h
  have hprev := st139_p193
  have hstep := st139_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p195 : ((2125018297419/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT139 (i+1))
      = (∑ i ∈ Finset.range 194, stT139 (i+1)) + stT139 195 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 194
    simpa using h
  have hprev := st139_p194
  have hstep := st139_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p196 : ((2030307545249/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT139 (i+1))
      = (∑ i ∈ Finset.range 195, stT139 (i+1)) + stT139 196 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 195
    simpa using h
  have hprev := st139_p195
  have hstep := st139_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p197 : ((10139152130381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT139 (i+1))
      = (∑ i ∈ Finset.range 196, stT139 (i+1)) + stT139 197 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 196
    simpa using h
  have hprev := st139_p196
  have hstep := st139_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p198 : ((2117908574629/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT139 (i+1))
      = (∑ i ∈ Finset.range 197, stT139 (i+1)) + stT139 198 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 197
    simpa using h
  have hprev := st139_p197
  have hstep := st139_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p199 : ((11286412593481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT139 (i+1))
      = (∑ i ∈ Finset.range 198, stT139 (i+1)) + stT139 199 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 198
    simpa using h
  have hprev := st139_p198
  have hstep := st139_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p200 : ((11902579812139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT139 (i+1))
      = (∑ i ∈ Finset.range 199, stT139 (i+1)) + stT139 200 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 199
    simpa using h
  have hprev := st139_p199
  have hstep := st139_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p201 : ((3038556260611/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT139 (i+1))
      = (∑ i ∈ Finset.range 200, stT139 (i+1)) + stT139 201 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 200
    simpa using h
  have hprev := st139_p200
  have hstep := st139_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p202 : ((2982388735869/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT139 (i+1))
      = (∑ i ∈ Finset.range 201, stT139 (i+1)) + stT139 202 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 201
    simpa using h
  have hprev := st139_p201
  have hstep := st139_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p203 : ((5667323019297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT139 (i+1))
      = (∑ i ∈ Finset.range 202, stT139 (i+1)) + stT139 203 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 202
    simpa using h
  have hprev := st139_p202
  have hstep := st139_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p204 : ((1329976688457/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT139 (i+1))
      = (∑ i ∈ Finset.range 203, stT139 (i+1)) + stT139 204 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 203
    simpa using h
  have hprev := st139_p203
  have hstep := st139_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p205 : ((5077426177679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT139 (i+1))
      = (∑ i ∈ Finset.range 204, stT139 (i+1)) + stT139 205 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 204
    simpa using h
  have hprev := st139_p204
  have hstep := st139_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p206 : ((5045731748019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT139 (i+1))
      = (∑ i ∈ Finset.range 205, stT139 (i+1)) + stT139 206 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 205
    simpa using h
  have hprev := st139_p205
  have hstep := st139_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p207 : ((5236766038343/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT139 (i+1))
      = (∑ i ∈ Finset.range 206, stT139 (i+1)) + stT139 207 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 206
    simpa using h
  have hprev := st139_p206
  have hstep := st139_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p208 : ((11131924227811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT139 (i+1))
      = (∑ i ∈ Finset.range 207, stT139 (i+1)) + stT139 208 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 207
    simpa using h
  have hprev := st139_p207
  have hstep := st139_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p209 : ((11782181732649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT139 (i+1))
      = (∑ i ∈ Finset.range 208, stT139 (i+1)) + stT139 209 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 208
    simpa using h
  have hprev := st139_p208
  have hstep := st139_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p210 : ((3037099634521/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT139 (i+1))
      = (∑ i ∈ Finset.range 209, stT139 (i+1)) + stT139 210 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 209
    simpa using h
  have hprev := st139_p209
  have hstep := st139_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p211 : ((3019763615443/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT139 (i+1))
      = (∑ i ∈ Finset.range 210, stT139 (i+1)) + stT139 211 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 210
    simpa using h
  have hprev := st139_p210
  have hstep := st139_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p212 : ((11606835504289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT139 (i+1))
      = (∑ i ∈ Finset.range 211, stT139 (i+1)) + stT139 212 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 211
    simpa using h
  have hprev := st139_p211
  have hstep := st139_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p213 : ((2186042821509/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT139 (i+1))
      = (∑ i ∈ Finset.range 212, stT139 (i+1)) + stT139 213 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 212
    simpa using h
  have hprev := st139_p212
  have hstep := st139_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p214 : ((10327816933179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT139 (i+1))
      = (∑ i ∈ Finset.range 213, stT139 (i+1)) + stT139 214 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 213
    simpa using h
  have hprev := st139_p213
  have hstep := st139_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p215 : ((5021635102657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT139 (i+1))
      = (∑ i ∈ Finset.range 214, stT139 (i+1)) + stT139 215 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 214
    simpa using h
  have hprev := st139_p214
  have hstep := st139_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p216 : ((10188186607293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT139 (i+1))
      = (∑ i ∈ Finset.range 215, stT139 (i+1)) + stT139 216 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 215
    simpa using h
  have hprev := st139_p215
  have hstep := st139_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p217 : ((10701147608609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT139 (i+1))
      = (∑ i ∈ Finset.range 216, stT139 (i+1)) + stT139 217 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 216
    simpa using h
  have hprev := st139_p216
  have hstep := st139_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p218 : ((11376494218939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT139 (i+1))
      = (∑ i ∈ Finset.range 217, stT139 (i+1)) + stT139 218 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 217
    simpa using h
  have hprev := st139_p217
  have hstep := st139_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p219 : ((597428421649/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT139 (i+1))
      = (∑ i ∈ Finset.range 218, stT139 (i+1)) + stT139 219 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 218
    simpa using h
  have hprev := st139_p218
  have hstep := st139_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p220 : ((2439269335693/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT139 (i+1))
      = (∑ i ∈ Finset.range 219, stT139 (i+1)) + stT139 220 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 219
    simpa using h
  have hprev := st139_p219
  have hstep := st139_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p221 : ((6013641550351/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT139 (i+1))
      = (∑ i ∈ Finset.range 220, stT139 (i+1)) + stT139 221 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 220
    simpa using h
  have hprev := st139_p220
  have hstep := st139_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p222 : ((11509307618597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT139 (i+1))
      = (∑ i ∈ Finset.range 221, stT139 (i+1)) + stT139 222 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 221
    simpa using h
  have hprev := st139_p221
  have hstep := st139_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p223 : ((10841018347397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT139 (i+1))
      = (∑ i ∈ Finset.range 222, stT139 (i+1)) + stT139 223 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 222
    simpa using h
  have hprev := st139_p222
  have hstep := st139_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p224 : ((10273962060983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT139 (i+1))
      = (∑ i ∈ Finset.range 223, stT139 (i+1)) + stT139 224 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 223
    simpa using h
  have hprev := st139_p223
  have hstep := st139_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p225 : ((39132234113/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT139 (i+1))
      = (∑ i ∈ Finset.range 224, stT139 (i+1)) + stT139 225 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 224
    simpa using h
  have hprev := st139_p224
  have hstep := st139_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p226 : ((5082190325659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT139 (i+1))
      = (∑ i ∈ Finset.range 225, stT139 (i+1)) + stT139 226 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 225
    simpa using h
  have hprev := st139_p225
  have hstep := st139_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p227 : ((266418491621/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT139 (i+1))
      = (∑ i ∈ Finset.range 226, stT139 (i+1)) + stT139 227 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 226
    simpa using h
  have hprev := st139_p226
  have hstep := st139_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p228 : ((707118145141/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT139 (i+1))
      = (∑ i ∈ Finset.range 227, stT139 (i+1)) + stT139 228 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 227
    simpa using h
  have hprev := st139_p227
  have hstep := st139_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p229 : ((1487333003761/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT139 (i+1))
      = (∑ i ∈ Finset.range 228, stT139 (i+1)) + stT139 229 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 228
    simpa using h
  have hprev := st139_p228
  have hstep := st139_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p230 : ((1525446486521/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT139 (i+1))
      = (∑ i ∈ Finset.range 229, stT139 (i+1)) + stT139 230 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 229
    simpa using h
  have hprev := st139_p229
  have hstep := st139_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p231 : ((1515412060569/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT139 (i+1))
      = (∑ i ∈ Finset.range 230, stT139 (i+1)) + stT139 231 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 230
    simpa using h
  have hprev := st139_p230
  have hstep := st139_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p232 : ((11689030762103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT139 (i+1))
      = (∑ i ∈ Finset.range 231, stT139 (i+1)) + stT139 232 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 231
    simpa using h
  have hprev := st139_p231
  have hstep := st139_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p233 : ((442171348457/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT139 (i+1))
      = (∑ i ∈ Finset.range 232, stT139 (i+1)) + stT139 233 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 232
    simpa using h
  have hprev := st139_p232
  have hstep := st139_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p234 : ((10439059033673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT139 (i+1))
      = (∑ i ∈ Finset.range 233, stT139 (i+1)) + stT139 234 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 233
    simpa using h
  have hprev := st139_p233
  have hstep := st139_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p235 : ((10053128150693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT139 (i+1))
      = (∑ i ∈ Finset.range 234, stT139 (i+1)) + stT139 235 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 234
    simpa using h
  have hprev := st139_p234
  have hstep := st139_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p236 : ((5012631574039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT139 (i+1))
      = (∑ i ∈ Finset.range 235, stT139 (i+1)) + stT139 236 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 235
    simpa using h
  have hprev := st139_p235
  have hstep := st139_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p237 : ((10361958794831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT139 (i+1))
      = (∑ i ∈ Finset.range 236, stT139 (i+1)) + stT139 237 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 236
    simpa using h
  have hprev := st139_p236
  have hstep := st139_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p238 : ((2189646236761/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT139 (i+1))
      = (∑ i ∈ Finset.range 237, stT139 (i+1)) + stT139 238 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 237
    simpa using h
  have hprev := st139_p237
  have hstep := st139_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p239 : ((11588512343751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT139 (i+1))
      = (∑ i ∈ Finset.range 238, stT139 (i+1)) + stT139 239 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 238
    simpa using h
  have hprev := st139_p238
  have hstep := st139_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p240 : ((1509081403897/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT139 (i+1))
      = (∑ i ∈ Finset.range 239, stT139 (i+1)) + stT139 240 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 239
    simpa using h
  have hprev := st139_p239
  have hstep := st139_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p241 : ((3061142023387/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT139 (i+1))
      = (∑ i ∈ Finset.range 240, stT139 (i+1)) + stT139 241 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 240
    simpa using h
  have hprev := st139_p240
  have hstep := st139_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p242 : ((94150632041/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT139 (i+1))
      = (∑ i ∈ Finset.range 241, stT139 (i+1)) + stT139 242 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 241
    simpa using h
  have hprev := st139_p241
  have hstep := st139_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p243 : ((5778705546191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT139 (i+1))
      = (∑ i ∈ Finset.range 242, stT139 (i+1)) + stT139 243 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 242
    simpa using h
  have hprev := st139_p242
  have hstep := st139_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p244 : ((2730476461183/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT139 (i+1))
      = (∑ i ∈ Finset.range 243, stT139 (i+1)) + stT139 244 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 243
    simpa using h
  have hprev := st139_p243
  have hstep := st139_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p245 : ((10345796593351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT139 (i+1))
      = (∑ i ∈ Finset.range 244, stT139 (i+1)) + stT139 245 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 244
    simpa using h
  have hprev := st139_p244
  have hstep := st139_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p246 : ((10008445676573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT139 (i+1))
      = (∑ i ∈ Finset.range 245, stT139 (i+1)) + stT139 246 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 245
    simpa using h
  have hprev := st139_p245
  have hstep := st139_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p247 : ((2002496961481/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT139 (i+1))
      = (∑ i ∈ Finset.range 246, stT139 (i+1)) + stT139 247 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 246
    simpa using h
  have hprev := st139_p246
  have hstep := st139_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p248 : ((2070811404481/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT139 (i+1))
      = (∑ i ∈ Finset.range 247, stT139 (i+1)) + stT139 248 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 247
    simpa using h
  have hprev := st139_p247
  have hstep := st139_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p249 : ((10926458085821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT139 (i+1))
      = (∑ i ∈ Finset.range 248, stT139 (i+1)) + stT139 249 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 248
    simpa using h
  have hprev := st139_p248
  have hstep := st139_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_p250 : ((11554798333591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT139 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT139 (i+1))
      = (∑ i ∈ Finset.range 249, stT139 (i+1)) + stT139 250 := by
    have h := Finset.sum_range_succ (fun i => stT139 (i+1)) 249
    simpa using h
  have hprev := st139_p249
  have hstep := st139_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st139_s250 :
    |Real.sin (((139 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))
      - ((113449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 142117/5000000) (δ := 6977/1000000000) (ψ := 820771/1000000) 139 122
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 139`** (evaluated boundary). -/
theorem station_139_sign : 0 < hardyG ((((139:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 139 250 (by norm_num) (by norm_num)
    ((820771/1000000 : ℚ) : ℝ)
  have hchain := st139_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT139 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((139 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((820771/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st139_c250
  have hsinb := abs_le.mp st139_s250
  have hbdy_lo : ((-643253526003/48303125000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((139 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((820771/1000000 : ℚ) : ℝ))) / 2
          - ((((139:ℕ)):ℝ))
            * Real.sin (((139 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((820771/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((139:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((139:ℝ) * Real.log (250:ℝ) - ((820771/1000000 : ℚ) : ℝ))) / 2
        - ((139:ℝ)) * Real.sin ((139:ℝ) * Real.log (250:ℝ) - ((820771/1000000 : ℚ) : ℝ))
        ≥ ((-8136579/500000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((139:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-8136579/500000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-8136579/500000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-8136579/500000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((139:ℕ)):ℝ))+1) * (((((139:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((14071118259/31250000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((11554798333591/10000000000000 : ℚ) : ℝ) + ((-643253526003/48303125000000 : ℚ) : ℝ)
      - ((14071118259/31250000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((820771/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((139:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((820771/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((139:ℕ)):ℝ)))).re
      - Real.sin ((820771/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((139:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((139:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((139:ℕ)):ℝ))
      = (((((139:ℕ)):ℝ)) * (Real.log ((((139:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((139:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_139
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
  have hθwin : |(((820771/1000000 : ℚ) : ℝ) + ((23:ℤ)) * (2*Real.pi)) - theta ((((139:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((139:ℕ)):ℝ)))
    (φ := ((820771/1000000 : ℚ) : ℝ) + ((23:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((820771/1000000 : ℚ)) : ℝ) 23).1,
    (cos_sin_shift (((820771/1000000 : ℚ)) : ℝ) 23).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_139_sign
end AxiomAudit
