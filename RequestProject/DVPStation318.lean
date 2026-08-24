import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 318` (rung-335.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT318 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((318 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-195723/500000 : ℚ) : ℝ))

theorem st318_c1 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((462179/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 195723/2000000) (δ := 1/1000000000) (ψ := -195723/500000) 318 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t1 : ((462129/500000 : ℚ) : ℝ) ≤ stT318 1 := by
  have hc : ((462129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((462129/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((462129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c2 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((621019/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 450377/2000000) (δ := 15953/1000000000) (ψ := -195723/500000) 318 35
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t2 : ((4390559850573/10000000000000 : ℚ) : ℝ) ≤ stT318 2 := by
  have hc : ((620919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4390559850573/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((620919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c3 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-255969/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5270589/10000000) (δ := 4001/250000000) (ψ := -195723/500000) 318 56
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t3 : ((-1478126464557/5000000000000 : ℚ) : ℝ) ≤ stT318 3 := by
  have hc : ((-256019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1478126464557/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-256019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c4 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((40007/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1762597/5000000) (δ := 16099/1000000000) (ψ := -195723/500000) 318 70
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t4 : ((19991/250000 : ℚ) : ℝ) ≤ stT318 4 := by
  have hc : ((19991/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19991/250000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((19991/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c5 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-99361/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7571203/10000000) (δ := 16013/1000000000) (ψ := -195723/500000) 318 82
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t5 : ((-55550078307/125000000000 : ℚ) : ℝ) ≤ stT318 5 := by
  have hc : ((-99371/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55550078307/125000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-99371/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c6 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-1757/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24983/62500) (δ := 1003/62500000) (ψ := -195723/500000) 318 91
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t6 : ((-28793752599/2500000000000 : ℚ) : ℝ) ≤ stT318 6 := by
  have hc : ((-7053/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28793752599/2500000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-7053/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c7 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-956183/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7111179/10000000) (δ := 4003/250000000) (ψ := -195723/500000) 318 99
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t7 : ((-722882051907/2000000000000 : ℚ) : ℝ) ≤ stT318 7 := by
  have hc : ((-956283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-722882051907/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-956283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c8 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-341587/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 599813/1250000) (δ := 3987/250000000) (ψ := -195723/500000) 318 105
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t8 : ((-604023002929/5000000000000 : ℚ) : ℝ) ≤ stT318 8 := by
  have hc : ((-341687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-604023002929/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-341687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c9 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-52149/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 418821/1000000) (δ := 8049/500000000) (ψ := -195723/500000) 318 111
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t9 : ((-86998350733/2500000000000 : ℚ) : ℝ) ≤ stT318 9 := by
  have hc : ((-52199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86998350733/2500000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-52199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c10 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-2539/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6297973/10000000) (δ := 16061/1000000000) (ψ := -195723/500000) 318 117
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t10 : ((-64240096431/250000000000 : ℚ) : ℝ) ≤ stT318 10 := by
  have hc : ((-40629/50000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64240096431/250000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-40629/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c11 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-884731/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6641783/10000000) (δ := 16033/1000000000) (ψ := -195723/500000) 318 121
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t11 : ((-1333933167867/5000000000000 : ℚ) : ℝ) ≤ stT318 11 := by
  have hc : ((-884831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1333933167867/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-884831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c12 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((462851/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -272397/1000000) (δ := 7953/500000000) (ψ := -195723/500000) 318 126
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t12 : ((1335846912001/10000000000000 : ℚ) : ℝ) ≤ stT318 12 := by
  have hc : ((462751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1335846912001/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((462751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c13 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((35939/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1921877/10000000) (δ := 4017/250000000) (ψ := -195723/500000) 318 130
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t13 : ((99662949/500000000 : ℚ) : ℝ) ≤ stT318 13 := by
  have hc : ((17967/25000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99662949/500000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((17967/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c14 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-692069/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -583787/1000000) (δ := 16039/1000000000) (ψ := -195723/500000) 318 134
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t14 : ((-1849899867597/10000000000000 : ℚ) : ℝ) ≤ stT318 14 := by
  have hc : ((-692169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1849899867597/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-692169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c15 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((145649/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 471899/2500000) (δ := 7959/500000000) (ψ := -195723/500000) 318 137
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t15 : ((94003082613/500000000000 : ℚ) : ℝ) ≤ stT318 15 := by
  have hc : ((145629/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94003082613/500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((145629/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c16 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-75649/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3035907/5000000) (δ := 16007/1000000000) (ψ := -195723/500000) 318 140
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t16 : ((-189147575659/1000000000000 : ℚ) : ℝ) ≤ stT318 16 := by
  have hc : ((-75659/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-189147575659/1000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-75659/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c17 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-479999/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7144481/10000000) (δ := 1991/125000000) (ψ := -195723/500000) 318 143
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t17 : ((-1164290202493/5000000000000 : ℚ) : ℝ) ≤ stT318 17 := by
  have hc : ((-480049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1164290202493/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-480049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c18 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-575987/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5461519/10000000) (δ := 15953/1000000000) (ψ := -195723/500000) 318 146
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t18 : ((-1357850309001/10000000000000 : ℚ) : ℝ) ≤ stT318 18 := by
  have hc : ((-576087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1357850309001/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-576087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c19 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((215901/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1321053/10000000) (δ := 501/31250000) (ψ := -195723/500000) 318 149
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t19 : ((123813359133/625000000000 : ℚ) : ℝ) ≤ stT318 19 := by
  have hc : ((53969/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123813359133/625000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((53969/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c20 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-425097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5024663/10000000) (δ := 1591/100000000) (ψ := -195723/500000) 318 152
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t20 : ((-237692351349/2500000000000 : ℚ) : ℝ) ≤ stT318 20 := by
  have hc : ((-425197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237692351349/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-425197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c21 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((590557/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2347619/10000000) (δ := 503/31250000) (ψ := -195723/500000) 318 154
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t21 : ((644241137673/5000000000000 : ℚ) : ℝ) ≤ stT318 21 := by
  have hc : ((590457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((644241137673/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((590457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c22 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-999701/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -779287/1000000) (δ := 16029/1000000000) (ψ := -195723/500000) 318 157
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t22 : ((-266447966301/1250000000000 : ℚ) : ℝ) ≤ stT318 22 := by
  have hc : ((-999801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-266447966301/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-999801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c23 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((5737/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241851/625000) (δ := 399/25000000) (ψ := -195723/500000) 318 159
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t23 : ((93049551/19531250000 : ℚ) : ℝ) ≤ stT318 23 := by
  have hc : ((357/15625 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93049551/19531250000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((357/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c24 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((418159/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72533/500000) (δ := 16057/1000000000) (ψ := -195723/500000) 318 161
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t24 : ((853461233269/5000000000000 : ℚ) : ℝ) ≤ stT318 24 := by
  have hc : ((418109/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((853461233269/5000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((418109/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c25 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((986379/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -413097/10000000) (δ := 15931/1000000000) (ψ := -195723/500000) 318 163
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t25 : ((986279/5000000 : ℚ) : ℝ) ≤ stT318 25 := by
  have hc : ((986279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((986279/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((986279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c26 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((966537/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -648567/10000000) (δ := 15917/1000000000) (ψ := -195723/500000) 318 165
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t26 : ((1895338553357/10000000000000 : ℚ) : ℝ) ≤ stT318 26 := by
  have hc : ((966437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1895338553357/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((966437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c27 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((679011/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -412191/2000000) (δ := 15903/1000000000) (ψ := -195723/500000) 318 167
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t27 : ((2613128439/20000000000 : ℚ) : ℝ) ≤ stT318 27 := by
  have hc : ((678911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2613128439/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((678911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c28 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-15767/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -57057/125000) (δ := 3183/200000000) (ψ := -195723/500000) 318 169
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t28 : ((-119234602539/2500000000000 : ℚ) : ℝ) ≤ stT318 28 := by
  have hc : ((-63093/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119234602539/2500000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-63093/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c29 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-995811/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 381253/500000) (δ := 15981/1000000000) (ψ := -195723/500000) 318 170
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t29 : ((-924680457547/5000000000000 : ℚ) : ℝ) ≤ stT318 29 := by
  have hc : ((-995911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-924680457547/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-995911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c30 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((301691/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1580413/5000000) (δ := 15967/1000000000) (ψ := -195723/500000) 318 172
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t30 : ((550627053931/10000000000000 : ℚ) : ℝ) ≤ stT318 30 := by
  have hc : ((301591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((550627053931/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((301591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c31 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((64111/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -218713/1000000) (δ := 997/62500000) (ψ := -195723/500000) 318 174
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t31 : ((115128793353/1000000000000 : ℚ) : ℝ) ≤ stT318 31 := by
  have hc : ((64101/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115128793353/1000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((64101/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c32 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-244839/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7345123/10000000) (δ := 3209/200000000) (ψ := -195723/500000) 318 175
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t32 : ((-3381738271/19531250000 : ℚ) : ℝ) ≤ stT318 32 := by
  have hc : ((-15304/15625 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3381738271/19531250000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-15304/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c33 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((987693/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 392619/10000000) (δ := 3993/250000000) (ψ := -195723/500000) 318 177
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t33 : ((214897274021/1250000000000 : ℚ) : ℝ) ≤ stT318 33 := by
  have hc : ((987593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214897274021/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((987593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c34 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-974677/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7290173/10000000) (δ := 1001/62500000) (ψ := -195723/500000) 318 179
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t34 : ((-835864454061/5000000000000 : ℚ) : ℝ) ≤ stT318 34 := by
  have hc : ((-974777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-835864454061/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-974777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c35 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((62489/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 46927/10000000) (δ := 8047/500000000) (ψ := -195723/500000) 318 180
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t35 : ((105615092187/625000000000 : ℚ) : ℝ) ≤ stT318 35 := by
  have hc : ((249931/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105615092187/625000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((249931/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c36 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-450731/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6734829/10000000) (δ := 16001/1000000000) (ψ := -195723/500000) 318 181
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t36 : ((-751301816927/5000000000000 : ℚ) : ℝ) ≤ stT318 36 := by
  have hc : ((-450781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-751301816927/5000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-450781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c37 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((79949/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2898893/10000000) (δ := 3997/250000000) (ψ := -195723/500000) 318 183
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t37 : ((131402396781/2000000000000 : ℚ) : ℝ) ≤ stT318 37 := by
  have hc : ((79929/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131402396781/2000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((79929/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c38 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((127041/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2594363/10000000) (δ := 15923/1000000000) (ψ := -195723/500000) 318 184
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t38 : ((12877945839/156250000000 : ℚ) : ℝ) ≤ stT318 38 := by
  have hc : ((15877/31250 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12877945839/156250000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((15877/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c39 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-991969/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3768461/5000000) (δ := 15973/1000000000) (ψ := -195723/500000) 318 185
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t39 : ((-794291116229/5000000000000 : ℚ) : ℝ) ≤ stT318 39 := by
  have hc : ((-992069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-794291116229/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-992069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c40 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((70197/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3751353/10000000) (δ := 4011/250000000) (ψ := -195723/500000) 318 187
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t40 : ((55416515193/5000000000000 : ℚ) : ℝ) ≤ stT318 40 := by
  have hc : ((70097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55416515193/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((70097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c41 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((997653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1713/100000) (δ := 4013/250000000) (ψ := -195723/500000) 318 188
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t41 : ((1557915429561/10000000000000 : ℚ) : ℝ) ≤ stT318 41 := by
  have hc : ((997553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1557915429561/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((997553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c42 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((122119/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3620929/10000000) (δ := 3189/200000000) (ψ := -195723/500000) 318 189
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t42 : ((188279343627/10000000000000 : ℚ) : ℝ) ≤ stT318 42 := by
  have hc : ((122019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188279343627/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((122019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c43 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-440291/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6619713/10000000) (δ := 16037/1000000000) (ψ := -195723/500000) 318 190
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t43 : ((-335756930113/2500000000000 : ℚ) : ℝ) ≤ stT318 43 := by
  have hc : ((-440341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-335756930113/2500000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-440341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c44 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-26903/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6519561/10000000) (δ := 16023/1000000000) (ψ := -195723/500000) 318 192
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t44 : ((-324500136693/2500000000000 : ℚ) : ℝ) ≤ stT318 44 := by
  have hc : ((-215249/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324500136693/2500000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-215249/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c45 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-43247/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -272603/625000) (δ := 3979/250000000) (ψ := -195723/500000) 318 193
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t45 : ((-1007907651/39062500000 : ℚ) : ℝ) ≤ stT318 45 := by
  have hc : ((-5409/31250 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1007907651/39062500000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-5409/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c46 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((253733/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1298193/5000000) (δ := 16009/1000000000) (ψ := -195723/500000) 318 194
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t46 : ((374035035177/5000000000000 : ℚ) : ℝ) ≤ stT318 46 := by
  have hc : ((253683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((374035035177/5000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((253683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c47 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((27679/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1206841/10000000) (δ := 16101/1000000000) (ψ := -195723/500000) 318 195
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t47 : ((322955099143/2500000000000 : ℚ) : ℝ) ≤ stT318 47 := by
  have hc : ((221407/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((322955099143/2500000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((221407/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c48 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((199497/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -177351/10000000) (δ := 7997/500000000) (ψ := -195723/500000) 318 196
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t48 : ((2303360919/16000000000 : ℚ) : ℝ) ≤ stT318 48 := by
  have hc : ((199477/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2303360919/16000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((199477/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c49 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((97951/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10139/200000) (δ := 3979/250000000) (ψ := -195723/500000) 318 197
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t49 : ((139915672311/1000000000000 : ℚ) : ℝ) ≤ stT318 49 := by
  have hc : ((97941/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139915672311/1000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((97941/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c50 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((117673/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 860213/10000000) (δ := 16023/1000000000) (ψ := -195723/500000) 318 198
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t50 : ((332794017373/2500000000000 : ℚ) : ℝ) ≤ stT318 50 := by
  have hc : ((235321/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((332794017373/2500000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((235321/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c51 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((187311/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 223829/2500000) (δ := 16073/1000000000) (ψ := -195723/500000) 318 199
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t51 : ((6556496037/50000000000 : ℚ) : ℝ) ≤ stT318 51 := by
  have hc : ((187291/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6556496037/50000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((187291/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c52 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((484469/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 624743/10000000) (δ := 16037/1000000000) (ψ := -195723/500000) 318 200
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t52 : ((2687072193/20000000000 : ℚ) : ℝ) ≤ stT318 52 := by
  have hc : ((484419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2687072193/20000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((484419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c53 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((999711/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30049/5000000) (δ := 8029/500000000) (ψ := -195723/500000) 318 201
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t53 : ((274614133531/2000000000000 : ℚ) : ℝ) ≤ stT318 53 := by
  have hc : ((999611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274614133531/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((999611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c54 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((475389/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -157529/2000000) (δ := 4013/250000000) (ψ := -195723/500000) 318 202
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t54 : ((646854145353/5000000000000 : ℚ) : ℝ) ≤ stT318 54 := by
  have hc : ((475339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((646854145353/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((475339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c55 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((722607/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -954037/5000000) (δ := 15959/1000000000) (ψ := -195723/500000) 318 203
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t55 : ((974227716293/10000000000000 : ℚ) : ℝ) ≤ stT318 55 := by
  have hc : ((722507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((974227716293/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((722507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c56 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((251533/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -329133/1000000) (δ := 15937/1000000000) (ψ := -195723/500000) 318 204
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t56 : ((167995713249/5000000000000 : ℚ) : ℝ) ≤ stT318 56 := by
  have hc : ((251433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167995713249/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((251433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c57 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-389831/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4928111/10000000) (δ := 15973/1000000000) (ψ := -195723/500000) 318 205
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t57 : ((-516476477223/10000000000000 : ℚ) : ℝ) ≤ stT318 57 := by
  have hc : ((-389931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-516476477223/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-389931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c58 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-457001/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6809593/10000000) (δ := 201/12500000) (ψ := -195723/500000) 318 206
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t58 : ((-120027534263/1000000000000 : ℚ) : ℝ) ≤ stT318 58 := by
  have hc : ((-457051/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120027534263/1000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-457051/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c59 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-909211/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1356091/2000000) (δ := 201/12500000) (ψ := -195723/500000) 318 206
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t59 : ((-118382289779/1000000000000 : ℚ) : ℝ) ≤ stT318 59 := by
  have hc : ((-909311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118382289779/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-909311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c60 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-20147/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 554267/1250000) (δ := 3997/250000000) (ψ := -195723/500000) 318 207
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t60 : ((-5204517243/200000000000 : ℚ) : ℝ) ≤ stT318 60 := by
  have hc : ((-20157/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5204517243/200000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-20157/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c61 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((183469/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 933483/5000000) (δ := 3977/250000000) (ψ := -195723/500000) 318 208
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t61 : ((3669934803/39062500000 : ℚ) : ℝ) ≤ stT318 61 := by
  have hc : ((45861/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3669934803/39062500000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((45861/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c62 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((233481/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9139/100000) (δ := 16001/1000000000) (ψ := -195723/500000) 318 209
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t62 : ((18530584591/156250000000 : ℚ) : ℝ) ≤ stT318 62 := by
  have hc : ((14591/15625 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18530584591/156250000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((14591/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c63 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((5089/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -780309/2000000) (δ := 15909/1000000000) (ψ := -195723/500000) 318 210
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t63 : ((6348540359/5000000000000 : ℚ) : ℝ) ≤ stT318 63 := by
  have hc : ((5039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6348540359/5000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((5039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c64 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-476811/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -708961/1000000) (δ := 15987/1000000000) (ψ := -195723/500000) 318 211
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t64 : ((-596076726861/5000000000000 : ℚ) : ℝ) ≤ stT318 64 := by
  have hc : ((-476861/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-596076726861/5000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-476861/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c65 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-125021/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5236229/10000000) (δ := 15987/1000000000) (ψ := -195723/500000) 318 211
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t65 : ((-19387569501/312500000000 : ℚ) : ℝ) ≤ stT318 65 := by
  have hc : ((-62523/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19387569501/312500000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-62523/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c66 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((78607/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 208241/1250000) (δ := 16079/1000000000) (ψ := -195723/500000) 318 212
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t66 : ((48373073829/500000000000 : ℚ) : ℝ) ≤ stT318 66 := by
  have hc : ((78597/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48373073829/500000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((78597/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c67 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((335677/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -260863/1250000) (δ := 16031/1000000000) (ψ := -195723/500000) 318 213
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t67 : ((205016746069/2500000000000 : ℚ) : ℝ) ≤ stT318 67 := by
  have hc : ((335627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205016746069/2500000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((335627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c68 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-741933/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6016863/10000000) (δ := 7969/500000000) (ψ := -195723/500000) 318 214
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t68 : ((-899847836407/10000000000000 : ℚ) : ℝ) ≤ stT318 68 := by
  have hc : ((-742033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-899847836407/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-742033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c69 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-308481/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5589183/10000000) (δ := 7969/500000000) (ψ := -195723/500000) 318 214
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t69 : ((-371427821129/5000000000000 : ℚ) : ℝ) ≤ stT318 69 := by
  have hc : ((-308531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-371427821129/5000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-308531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c70 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((863769/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 330059/2500000) (δ := 7979/500000000) (ψ := -195723/500000) 318 215
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t70 : ((258070342883/2500000000000 : ℚ) : ℝ) ≤ stT318 70 := by
  have hc : ((863669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258070342883/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((863669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c71 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((320643/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -311097/1000000) (δ := 997/62500000) (ψ := -195723/500000) 318 216
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t71 : ((380414342083/10000000000000 : ℚ) : ℝ) ≤ stT318 71 := by
  have hc : ((320543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((380414342083/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((320543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c72 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-998099/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -307993/400000) (δ := 1993/125000000) (ψ := -195723/500000) 318 217
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t72 : ((-73524343743/625000000000 : ℚ) : ℝ) ≤ stT318 72 := by
  have hc : ((-998199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73524343743/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-998199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c73 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((52277/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3265849/10000000) (δ := 16059/1000000000) (ψ := -195723/500000) 318 217
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t73 : ((61162167627/2000000000000 : ℚ) : ℝ) ≤ stT318 73 := by
  have hc : ((52257/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61162167627/2000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((52257/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c74 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((795923/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1625663/10000000) (δ := 4009/250000000) (ψ := -195723/500000) 318 218
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t74 : ((231281284437/2500000000000 : ℚ) : ℝ) ≤ stT318 74 := by
  have hc : ((795823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231281284437/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((795823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c75 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-888519/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6662261/10000000) (δ := 8037/500000000) (ψ := -195723/500000) 318 219
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t75 : ((-1026089247919/10000000000000 : ℚ) : ℝ) ≤ stT318 75 := by
  have hc : ((-888619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1026089247919/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-888619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c76 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((949/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3867673/10000000) (δ := 8037/500000000) (ψ := -195723/500000) 318 219
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t76 : ((108398871/40000000000 : ℚ) : ℝ) ≤ stT318 76 := by
  have hc : ((189/8000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108398871/40000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((189/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c77 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((836907/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1447971/10000000) (δ := 15981/1000000000) (ψ := -195723/500000) 318 220
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t77 : ((190725888247/2000000000000 : ℚ) : ℝ) ≤ stT318 77 := by
  have hc : ((836807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190725888247/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((836807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c78 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-463867/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6897731/10000000) (δ := 2011/125000000) (ψ := -195723/500000) 318 221
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t78 : ((-262641506463/2500000000000 : ℚ) : ℝ) ≤ stT318 78 := by
  have hc : ((-463917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-262641506463/2500000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-463917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c79 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((137643/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1614887/5000000) (δ := 2011/125000000) (ψ := -195723/500000) 318 221
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t79 : ((154804095591/5000000000000 : ℚ) : ℝ) ≤ stT318 79 := by
  have hc : ((137593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154804095591/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((137593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c80 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((68459/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -619511/2500000) (δ := 2001/125000000) (ψ := -195723/500000) 318 222
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t80 : ((153050891469/2500000000000 : ℚ) : ℝ) ≤ stT318 80 := by
  have hc : ((136893/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153050891469/2500000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((136893/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c81 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-983401/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1849461/2500000) (δ := 3199/200000000) (ψ := -195723/500000) 318 222
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t81 : ((-136597470389/1250000000000 : ℚ) : ℝ) ≤ stT318 81 := by
  have hc : ((-983501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136597470389/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-983501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c82 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((418821/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 144461/1000000) (δ := 15903/1000000000) (ψ := -195723/500000) 318 223
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t82 : ((92491019373/1000000000000 : ℚ) : ℝ) ≤ stT318 82 := by
  have hc : ((418771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92491019373/1000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((418771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c83 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-138149/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115671/250000) (δ := 1601/100000000) (ψ := -195723/500000) 318 224
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t83 : ((-151693164957/5000000000000 : ℚ) : ℝ) ≤ stT318 83 := by
  have hc : ((-138199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151693164957/5000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-138199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c84 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-47163/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4894199/10000000) (δ := 3181/100000000) (ψ := -195723/500000) 318 224
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t84 : ((-10294543259/250000000000 : ℚ) : ℝ) ≤ stT318 84 := by
  have hc : ((-94351/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10294543259/250000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-94351/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c85 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((846111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1405377/10000000) (δ := 8043/500000000) (ψ := -195723/500000) 318 225
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t85 : ((229406880793/2500000000000 : ℚ) : ℝ) ≤ stT318 85 := by
  have hc : ((846011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229406880793/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((846011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c86 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-999879/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -390751/500000) (δ := 15979/1000000000) (ψ := -195723/500000) 318 226
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t86 : ((-134788169389/1250000000000 : ℚ) : ℝ) ≤ stT318 86 := by
  have hc : ((-999979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134788169389/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-999979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c87 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((852337/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 171987/1250000) (δ := 2003/125000000) (ψ := -195723/500000) 318 226
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t87 : ((57105844659/625000000000 : ℚ) : ℝ) ≤ stT318 87 := by
  have hc : ((852237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57105844659/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((852237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c88 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-503551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5246251/10000000) (δ := 15931/1000000000) (ψ := -195723/500000) 318 227
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t88 : ((-134223495151/2500000000000 : ℚ) : ℝ) ≤ stT318 88 := by
  have hc : ((-503651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134223495151/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-503651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c89 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((75983/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3736851/10000000) (δ := 2009/125000000) (ψ := -195723/500000) 318 227
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t89 : ((80435752351/10000000000000 : ℚ) : ℝ) ≤ stT318 89 := by
  have hc : ((75883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80435752351/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((75883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c90 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((65841/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1544169/5000000) (δ := 8019/500000000) (ψ := -195723/500000) 318 228
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t90 : ((17345347383/500000000000 : ℚ) : ℝ) ≤ stT318 90 := by
  have hc : ((65821/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17345347383/500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((65821/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c91 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-650103/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1424073/2500000) (δ := 6393/200000000) (ψ := -195723/500000) 318 228
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t91 : ((-136319610371/2000000000000 : ℚ) : ℝ) ≤ stT318 91 := by
  have hc : ((-650203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136319610371/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-650203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c92 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((215799/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -330769/2500000) (δ := 7973/500000000) (ψ := -195723/500000) 318 229
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t92 : ((28119991341/312500000000 : ℚ) : ℝ) ≤ stT318 92 := by
  have hc : ((107887/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28119991341/312500000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((107887/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c93 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-243247/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7271589/10000000) (δ := 16057/1000000000) (ψ := -195723/500000) 318 229
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t93 : ((-3941584171/39062500000 : ℚ) : ℝ) ≤ stT318 93 := by
  have hc : ((-30409/31250 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3941584171/39062500000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-30409/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c94 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((999647/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6639/1000000) (δ := 16053/1000000000) (ψ := -195723/500000) 318 230
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t94 : ((1030953766287/10000000000000 : ℚ) : ℝ) ≤ stT318 94 := by
  have hc : ((999547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1030953766287/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((999547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c95 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-193779/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1807201/2500000) (δ := 399/25000000) (ψ := -195723/500000) 318 231
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t95 : ((-198833704221/2000000000000 : ℚ) : ℝ) ≤ stT318 95 := by
  have hc : ((-193799/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198833704221/2000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-193799/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c96 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((905453/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1095879/10000000) (δ := 16043/1000000000) (ψ := -195723/500000) 318 231
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t96 : ((46201068943/500000000000 : ℚ) : ℝ) ≤ stT318 96 := by
  have hc : ((905353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46201068943/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((905353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c97 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-414877/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3186829/5000000) (δ := 249/15625000) (ψ := -195723/500000) 318 232
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t97 : ((-421294884669/5000000000000 : ℚ) : ℝ) ≤ stT318 97 := by
  have hc : ((-414927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-421294884669/5000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-414927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c98 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((756989/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 89013/500000) (δ := 16067/1000000000) (ψ := -195723/500000) 318 232
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t98 : ((95571617141/1250000000000 : ℚ) : ℝ) ≤ stT318 98 := by
  have hc : ((756889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95571617141/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((756889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c99 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-348721/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2928273/5000000) (δ := 16029/1000000000) (ψ := -195723/500000) 318 233
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t99 : ((-175264054149/2500000000000 : ℚ) : ℝ) ≤ stT318 99 := by
  have hc : ((-348771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175264054149/2500000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-348771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c100 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((328721/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2133443/10000000) (δ := 7987/500000000) (ψ := -195723/500000) 318 233
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t100 : ((328670671329/5000000000000 : ℚ) : ℝ) ≤ stT318 100 := by
  have hc : ((328671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((328670671329/5000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((328671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c101 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-32011/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -353997/625000) (δ := 8041/500000000) (ψ := -195723/500000) 318 234
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t101 : ((-995535519/15625000000 : ℚ) : ℝ) ≤ stT318 101 := by
  have hc : ((-2001/3125 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-995535519/15625000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-2001/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c102 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((646773/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1084313/5000000) (δ := 15921/1000000000) (ψ := -195723/500000) 318 234
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t102 : ((640301330931/10000000000000 : ℚ) : ℝ) ≤ stT318 102 := by
  have hc : ((646673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((640301330931/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((646673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c103 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-676131/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2891619/5000000) (δ := 8007/500000000) (ψ := -195723/500000) 318 235
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t103 : ((-66631069123/1000000000000 : ℚ) : ℝ) ≤ stT318 103 := by
  have hc : ((-676231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66631069123/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-676231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c104 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((362697/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1897973/10000000) (δ := 15989/1000000000) (ψ := -195723/500000) 318 235
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t104 : ((17780219763/250000000000 : ℚ) : ℝ) ≤ stT318 104 := by
  have hc : ((362647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17780219763/250000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((362647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c105 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-197391/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3101119/5000000) (δ := 15907/1000000000) (ψ := -195723/500000) 318 236
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t105 : ((-24082308977/312500000000 : ℚ) : ℝ) ≤ stT318 105 := by
  have hc : ((-24677/31250 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24082308977/312500000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-24677/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c106 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((430559/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1333329/10000000) (δ := 503/31250000) (ψ := -195723/500000) 318 236
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t106 : ((83629386813/1000000000000 : ℚ) : ℝ) ≤ stT318 106 := by
  have hc : ((430509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83629386813/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((430509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c107 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-929517/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -431859/625000) (δ := 1/62500) (ψ := -195723/500000) 318 237
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t107 : ((-898695149729/10000000000000 : ℚ) : ℝ) ≤ stT318 107 := by
  have hc : ((-929617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-898695149729/10000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-929617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c108 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((98119/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15177/312500) (δ := 1/62500) (ψ := -195723/500000) 318 237
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t108 : ((377621541/4000000000 : ℚ) : ℝ) ≤ stT318 108 := by
  have hc : ((98109/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((377621541/4000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((98109/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c109 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-199973/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7812861/10000000) (δ := 1/62500) (ψ := -195723/500000) 318 237
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t109 : ((-191558695211/2000000000000 : ℚ) : ℝ) ≤ stT318 109 := by
  have hc : ((-199993/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191558695211/2000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-199993/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c110 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((967939/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -126953/2000000) (δ := 16093/1000000000) (ψ := -195723/500000) 318 238
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t110 : ((461398854309/5000000000000 : ℚ) : ℝ) ≤ stT318 110 := by
  have hc : ((967839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((461398854309/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((967839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c111 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-434497/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3279953/5000000) (δ := 1591/100000000) (ψ := -195723/500000) 318 238
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t111 : ((-206226880713/2500000000000 : ℚ) : ℝ) ≤ stT318 111 := by
  have hc : ((-434547/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206226880713/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-434547/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c112 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((345759/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -100901/500000) (δ := 16017/1000000000) (ψ := -195723/500000) 318 239
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t112 : ((326664236899/5000000000000 : ℚ) : ℝ) ≤ stT318 112 := by
  have hc : ((345709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((326664236899/5000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((345709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c113 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-6778/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1009747/2000000) (δ := 16017/1000000000) (ψ := -195723/500000) 318 239
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t113 : ((-102042829033/2500000000000 : ℚ) : ℝ) ≤ stT318 113 := by
  have hc : ((-108473/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102042829033/2500000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-108473/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c114 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((108661/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1827401/5000000) (δ := 8039/500000000) (ψ := -195723/500000) 318 240
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t114 : ((20335320837/2000000000000 : ℚ) : ℝ) ≤ stT318 114 := by
  have hc : ((108561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20335320837/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((108561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c115 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((252633/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 328849/1000000) (δ := 637/40000000) (ψ := -195723/500000) 318 240
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t115 : ((29436004079/1250000000000 : ℚ) : ℝ) ≤ stT318 115 := by
  have hc : ((252533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29436004079/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((252533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c116 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-300099/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5536363/10000000) (δ := 501/31250000) (ψ := -195723/500000) 318 241
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t116 : ((-278681443073/5000000000000 : ℚ) : ℝ) ≤ stT318 116 := by
  have hc : ((-300149/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278681443073/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-300149/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c117 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((435121/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 643879/5000000) (δ := 501/31250000) (ψ := -195723/500000) 318 241
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t117 : ((804446279/10000000000 : ℚ) : ℝ) ≤ stT318 117 := by
  have hc : ((435071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((804446279/10000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((435071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c118 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-996809/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7654199/10000000) (δ := 15939/1000000000) (ψ := -195723/500000) 318 242
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t118 : ((-36709180107/400000000000 : ℚ) : ℝ) ≤ stT318 118 := by
  have hc : ((-996909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36709180107/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-996909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c119 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((116169/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -945353/10000000) (δ := 15939/1000000000) (ψ := -195723/500000) 318 242
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t119 : ((106480431237/1250000000000 : ℚ) : ℝ) ≤ stT318 119 := by
  have hc : ((232313/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106480431237/1250000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((232313/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c120 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-653487/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1141489/2000000) (δ := 251/15625000) (ψ := -195723/500000) 318 242
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t120 : ((-596640618277/10000000000000 : ℚ) : ℝ) ≤ stT318 120 := by
  have hc : ((-653587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-596640618277/10000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-653587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c121 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((52019/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -850743/2500000) (δ := 15957/1000000000) (ψ := -195723/500000) 318 243
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t121 : ((2363361273/125000000000 : ℚ) : ℝ) ≤ stT318 121 := by
  have hc : ((25997/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2363361273/125000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((25997/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c122 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((154759/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 785069/2500000) (δ := 8023/500000000) (ψ := -195723/500000) 318 243
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t122 : ((140066876113/5000000000000 : ℚ) : ℝ) ≤ stT318 122 := by
  have hc : ((154709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140066876113/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((154709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c123 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-75807/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -759733/1250000) (δ := 15953/1000000000) (ψ := -195723/500000) 318 244
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t123 : ((-6836191439/100000000000 : ℚ) : ℝ) ≤ stT318 123 := by
  have hc : ((-75817/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6836191439/100000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-75817/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c124 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((247421/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 35941/1000000) (δ := 15953/1000000000) (ψ := -195723/500000) 318 244
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t124 : ((27771005037/312500000000 : ℚ) : ℝ) ≤ stT318 124 := by
  have hc : ((61849/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27771005037/312500000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((61849/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c125 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-903217/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6745009/10000000) (δ := 15953/1000000000) (ψ := -195723/500000) 318 244
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t125 : ((-201988004419/2500000000000 : ℚ) : ℝ) ≤ stT318 125 := by
  have hc : ((-903317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-201988004419/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-903317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c126 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((7757/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -525647/2000000) (δ := 803/50000000) (ψ := -195723/500000) 318 245
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t126 : ((11054538569/250000000000 : ℚ) : ℝ) ≤ stT318 126 := by
  have hc : ((124087/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11054538569/250000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((124087/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c127 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((108057/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3656319/10000000) (δ := 15943/1000000000) (ψ := -195723/500000) 318 245
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t127 : ((23949072923/2500000000000 : ℚ) : ℝ) ≤ stT318 127 := by
  have hc : ((107957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23949072923/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((107957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c128 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-85727/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58163/100000) (δ := 499/31250000) (ψ := -195723/500000) 318 246
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t128 : ((-37891886109/625000000000 : ℚ) : ℝ) ≤ stT318 128 := by
  have hc : ((-171479/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37891886109/625000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-171479/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c129 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((247259/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 370549/10000000) (δ := 499/31250000) (ψ := -195723/500000) 318 246
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t129 : ((2176771753/25000000000 : ℚ) : ℝ) ≤ stT318 129 := by
  have hc : ((123617/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2176771753/25000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((123617/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c130 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-858849/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6509539/10000000) (δ := 499/31250000) (ψ := -195723/500000) 318 246
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t130 : ((-753348950991/10000000000000 : ℚ) : ℝ) ≤ stT318 130 := by
  have hc : ((-858949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-753348950991/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-858949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c131 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((322367/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3106419/10000000) (δ := 1991/125000000) (ψ := -195723/500000) 318 247
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t131 : ((35195745871/1250000000000 : ℚ) : ℝ) ≤ stT318 131 := by
  have hc : ((322267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35195745871/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((322267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c132 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((192451/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1469619/5000000) (δ := 1991/125000000) (ψ := -195723/500000) 318 247
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t132 : ((41865880397/1250000000000 : ℚ) : ℝ) ≤ stT318 132 := by
  have hc : ((192401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41865880397/1250000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((192401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c133 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-226811/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6768701/10000000) (δ := 7991/500000000) (ψ := -195723/500000) 318 248
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t133 : ((-4917294099/62500000000 : ℚ) : ℝ) ≤ stT318 133 := by
  have hc : ((-56709/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4917294099/62500000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-56709/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c134 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((473753/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -406817/5000000) (δ := 15991/500000000) (ψ := -195723/500000) 318 248
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t134 : ((102304215801/1250000000000 : ℚ) : ℝ) ≤ stT318 134 := by
  have hc : ((473703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102304215801/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((473703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c135 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-451159/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5097151/10000000) (δ := 7991/500000000) (ψ := -195723/500000) 318 248
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t135 : ((-388381924717/10000000000000 : ℚ) : ℝ) ≤ stT318 135 := by
  have hc : ((-451259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-388381924717/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-451259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c136 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-160439/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4743633/10000000) (δ := 7957/500000000) (ψ := -195723/500000) 318 249
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t136 : ((-137618194077/5000000000000 : ℚ) : ℝ) ≤ stT318 136 := by
  have hc : ((-160489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137618194077/5000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-160489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c137 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((908027/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1080617/10000000) (δ := 16089/1000000000) (ψ := -195723/500000) 318 249
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t137 : ((775693787939/10000000000000 : ℚ) : ℝ) ≤ stT318 137 := by
  have hc : ((907927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((775693787939/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((907927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c138 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-922369/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6862413/10000000) (δ := 7957/500000000) (ψ := -195723/500000) 318 249
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t138 : ((-785258193533/10000000000000 : ℚ) : ℝ) ≤ stT318 138 := by
  have hc : ((-922469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-785258193533/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-922469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c139 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((80687/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -776353/2500000) (δ := 16007/1000000000) (ψ := -195723/500000) 318 250
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t139 : ((8552067557/312500000000 : ℚ) : ℝ) ≤ stT318 139 := by
  have hc : ((40331/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8552067557/312500000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((40331/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c140 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((101689/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1296773/5000000) (δ := 3999/250000000) (ψ := -195723/500000) 318 250
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t140 : ((42962981013/1000000000000 : ℚ) : ℝ) ≤ stT318 140 := by
  have hc : ((101669/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42962981013/1000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((101669/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c141 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-987361/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1491217/2000000) (δ := 16099/1000000000) (ψ := -195723/500000) 318 251
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t141 : ((-103949032009/1250000000000 : ℚ) : ℝ) ≤ stT318 141 := by
  have hc : ((-987461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103949032009/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-987461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c142 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((185447/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1837661/10000000) (δ := 16099/1000000000) (ψ := -195723/500000) 318 251
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t142 : ((77801309691/1250000000000 : ℚ) : ℝ) ≤ stT318 142 := by
  have hc : ((92711/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77801309691/1250000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((92711/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c143 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((18549/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3741331/10000000) (δ := 16099/1000000000) (ψ := -195723/500000) 318 251
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t143 : ((1936318351/312500000000 : ℚ) : ℝ) ≤ stT318 143 := by
  have hc : ((4631/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1936318351/312500000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((4631/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c144 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-168277/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1285319/2000000) (δ := 1999/125000000) (ψ := -195723/500000) 318 252
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t144 : ((-70123806099/1000000000000 : ℚ) : ℝ) ≤ stT318 144 := by
  have hc : ((-168297/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70123806099/1000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-168297/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c145 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((932357/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -924797/10000000) (δ := 16011/1000000000) (ψ := -195723/500000) 318 252
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t145 : ((387098277339/5000000000000 : ℚ) : ℝ) ≤ stT318 145 := by
  have hc : ((932257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((387098277339/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((932257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c146 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-242427/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2269579/5000000) (δ := 1999/125000000) (ψ := -195723/500000) 318 252
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t146 : ((-100358400181/5000000000000 : ℚ) : ℝ) ≤ stT318 146 := by
  have hc : ((-242527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100358400181/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-242527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c147 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-663951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1148443/2000000) (δ := 3217/200000000) (ψ := -195723/500000) 318 253
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t147 : ((-547700632137/10000000000000 : ℚ) : ℝ) ≤ stT318 147 := by
  have hc : ((-664051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-547700632137/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-664051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c148 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((247521/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -352353/10000000) (δ := 7959/500000000) (ψ := -195723/500000) 318 253
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t148 : ((12715014189/156250000000 : ℚ) : ℝ) ≤ stT318 148 := by
  have hc : ((30937/31250 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12715014189/156250000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((30937/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c149 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-104151/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 625157/1250000) (δ := 3217/200000000) (ψ := -195723/500000) 318 253
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t149 : ((-166688111/4882812500 : ℚ) : ℝ) ≤ stT318 149 := by
  have hc : ((-6511/15625 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166688111/4882812500 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-6511/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c150 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-276023/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5389031/10000000) (δ := 641/40000000) (ψ := -195723/500000) 318 254
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t150 : ((-225412776281/5000000000000 : ℚ) : ℝ) ≤ stT318 150 := by
  have hc : ((-276073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225412776281/5000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-276073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c151 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((999091/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53287/5000000) (δ := 641/40000000) (ψ := -195723/500000) 318 254
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t151 : ((203241721977/2500000000000 : ℚ) : ℝ) ≤ stT318 151 := by
  have hc : ((998991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203241721977/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((998991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c152 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-29171/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2570491/5000000) (δ := 7989/500000000) (ψ := -195723/500000) 318 254
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t152 : ((-23665900893/625000000000 : ℚ) : ℝ) ≤ stT318 152 := by
  have hc : ((-116709/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23665900893/625000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-116709/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c153 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-540257/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -669231/1250000) (δ := 3983/250000000) (ψ := -195723/500000) 318 255
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t153 : ((-436853237721/10000000000000 : ℚ) : ℝ) ≤ stT318 153 := by
  have hc : ((-540357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-436853237721/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-540357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c154 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((24939/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87331/5000000) (δ := 16071/1000000000) (ψ := -195723/500000) 318 255
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t154 : ((20094380303/250000000000 : ℚ) : ℝ) ≤ stT318 154 := by
  have hc : ((49873/50000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20094380303/250000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((49873/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c155 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-202781/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 155343/312500) (δ := 3983/250000000) (ψ := -195723/500000) 318 255
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t155 : ((-8145895791/250000000000 : ℚ) : ℝ) ≤ stT318 155 := by
  have hc : ((-202831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8145895791/250000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-202831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c156 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-313997/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2812211/5000000) (δ := 3991/250000000) (ψ := -195723/500000) 318 256
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t156 : ((-251438904127/5000000000000 : ℚ) : ℝ) ≤ stT318 156 := by
  have hc : ((-314047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251438904127/5000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-314047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c157 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((976373/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -544531/10000000) (δ := 3991/250000000) (ψ := -195723/500000) 318 256
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t157 : ((389574906739/5000000000000 : ℚ) : ℝ) ≤ stT318 157 := by
  have hc : ((976273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((389574906739/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((976273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c158 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-228403/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4503083/10000000) (δ := 3991/250000000) (ψ := -195723/500000) 318 256
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t158 : ((-90893694837/5000000000000 : ℚ) : ℝ) ≤ stT318 158 := by
  have hc : ((-228503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90893694837/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-228503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c159 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-9829/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3094533/5000000) (δ := 15947/1000000000) (ψ := -195723/500000) 318 257
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t159 : ((-7795899423/125000000000 : ℚ) : ℝ) ≤ stT318 159 := by
  have hc : ((-39321/50000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7795899423/125000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-39321/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c160 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((886119/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -602367/5000000) (δ := 15947/1000000000) (ψ := -195723/500000) 318 257
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t160 : ((700459154811/10000000000000 : ℚ) : ℝ) ≤ stT318 160 := by
  have hc : ((886019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((700459154811/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((886019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c161 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((7133/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3748513/10000000) (δ := 2007/125000000) (ψ := -195723/500000) 318 257
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t161 : ((561370753/100000000000 : ℚ) : ℝ) ≤ stT318 161 := by
  have hc : ((7123/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((561370753/100000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((7123/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c162 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-236763/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -703681/1000000) (δ := 15949/1000000000) (ψ := -195723/500000) 318 258
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t162 : ((-1860384119/25000000000 : ℚ) : ℝ) ≤ stT318 162 := by
  have hc : ((-59197/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1860384119/25000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-59197/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c163 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((163529/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2144459/10000000) (δ := 8027/500000000) (ψ := -195723/500000) 318 258
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t163 : ((400206697/7812500000 : ℚ) : ℝ) ≤ stT318 163 := by
  have hc : ((10219/15625 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((400206697/7812500000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((10219/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c164 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((232497/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16987/62500) (δ := 8027/500000000) (ψ := -195723/500000) 318 258
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t164 : ((45377605999/1250000000000 : ℚ) : ℝ) ≤ stT318 164 := by
  have hc : ((232447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45377605999/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((232447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c165 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-248163/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 302029/400000) (δ := 8027/500000000) (ψ := -195723/500000) 318 258
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t165 : ((-48303527453/625000000000 : ℚ) : ℝ) ≤ stT318 165 := by
  have hc : ((-62047/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48303527453/625000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-62047/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c166 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((227347/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -335361/1000000) (δ := 15961/1000000000) (ψ := -195723/500000) 318 259
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t166 : ((3527555181/200000000000 : ℚ) : ℝ) ≤ stT318 166 := by
  have hc : ((227247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3527555181/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((227247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c167 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((105339/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1421239/10000000) (δ := 8021/500000000) (ψ := -195723/500000) 318 259
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t167 : ((163008136419/2500000000000 : ℚ) : ℝ) ≤ stT318 167 := by
  have hc : ((210653/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163008136419/2500000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((210653/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c168 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-390477/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6167469/10000000) (δ := 15961/1000000000) (ψ := -195723/500000) 318 259
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t168 : ((-301298219459/5000000000000 : ℚ) : ℝ) ≤ stT318 168 := by
  have hc : ((-390527/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-301298219459/5000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-390527/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c169 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-5477/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -602791/1250000) (δ := 4017/250000000) (ψ := -195723/500000) 318 260
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t169 : ((-67428481767/2500000000000 : ℚ) : ℝ) ≤ stT318 169 := by
  have hc : ((-87657/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67428481767/2500000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-87657/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c170 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((199721/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -132067/10000000) (δ := 3187/200000000) (ψ := -195723/500000) 318 260
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t170 : ((38290869441/500000000000 : ℚ) : ℝ) ≤ stT318 170 := by
  have hc : ((199701/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38290869441/500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((199701/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c171 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-239139/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 35396/78125) (δ := 4017/250000000) (ψ := -195723/500000) 318 260
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t171 : ((-2286885601/125000000000 : ℚ) : ℝ) ≤ stT318 171 := by
  have hc : ((-239239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2286885601/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-239239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c172 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-86537/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -654171/1000000) (δ := 639/40000000) (ψ := -195723/500000) 318 261
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t172 : ((-65991481671/1000000000000 : ℚ) : ℝ) ≤ stT318 172 := by
  have hc : ((-86547/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65991481671/1000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-86547/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c173 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((28627/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241627/1250000) (δ := 4007/250000000) (ψ := -195723/500000) 318 261
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t173 : ((4352327511/80000000000 : ℚ) : ℝ) ≤ stT318 173 := by
  have hc : ((28623/40000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4352327511/80000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((28623/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c174 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((489177/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1324563/5000000) (δ := 639/40000000) (ψ := -195723/500000) 318 261
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t174 : ((185384147773/5000000000000 : ℚ) : ℝ) ≤ stT318 174 := by
  have hc : ((489077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185384147773/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((489077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c175 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-483249/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 900629/1250000) (δ := 4007/250000000) (ψ := -195723/500000) 318 261
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t175 : ((-365339729771/5000000000000 : ℚ) : ℝ) ≤ stT318 175 := by
  have hc : ((-483299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-365339729771/5000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-483299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c176 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-18411/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3973021/10000000) (δ := 199/12500000) (ψ := -195723/500000) 318 262
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t176 : ((-13953203069/10000000000000 : ℚ) : ℝ) ≤ stT318 176 := by
  have hc : ((-18511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13953203069/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-18511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c177 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((977503/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 53129/1000000) (δ := 199/12500000) (ψ := -195723/500000) 318 262
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t177 : ((367330527669/5000000000000 : ℚ) : ℝ) ≤ stT318 177 := by
  have hc : ((977403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((367330527669/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((977403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c178 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-419839/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5010161/10000000) (δ := 199/12500000) (ψ := -195723/500000) 318 262
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t178 : ((-78689429637/2500000000000 : ℚ) : ℝ) ≤ stT318 178 := by
  have hc : ((-419939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78689429637/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-419939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c179 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-799699/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3121987/5000000) (δ := 16013/1000000000) (ψ := -195723/500000) 318 263
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t179 : ((-149449641341/2500000000000 : ℚ) : ℝ) ≤ stT318 179 := by
  have hc : ((-799799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149449641341/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-799799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c180 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((186957/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1815029/10000000) (δ := 16013/1000000000) (ψ := -195723/500000) 318 263
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t180 : ((6966535043/125000000000 : ℚ) : ℝ) ≤ stT318 180 := by
  have hc : ((46733/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6966535043/125000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((46733/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c181 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((254931/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 258943/1000000) (δ := 16013/1000000000) (ψ := -195723/500000) 318 263
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t181 : ((94725759007/2500000000000 : ℚ) : ℝ) ≤ stT318 181 := by
  have hc : ((254881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94725759007/2500000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((254881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c182 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-469037/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3484781/5000000) (δ := 16013/1000000000) (ψ := -195723/500000) 318 263
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t182 : ((-278168591/4000000000 : ℚ) : ℝ) ≤ stT318 182 := by
  have hc : ((-469087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278168591/4000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-469087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c183 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-90539/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2191099/5000000) (δ := 16097/1000000000) (ψ := -195723/500000) 318 264
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t183 : ((-33482690879/2500000000000 : ℚ) : ℝ) ≤ stT318 183 := by
  have hc : ((-90589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33482690879/2500000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-90589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c184 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((499901/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24883/5000000) (δ := 16097/1000000000) (ψ := -195723/500000) 318 264
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t184 : ((368494655859/5000000000000 : ℚ) : ℝ) ≤ stT318 184 := by
  have hc : ((499851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((368494655859/5000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((499851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c185 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-66249/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4259213/10000000) (δ := 7953/500000000) (ψ := -195723/500000) 318 264
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t185 : ((-9748803857/1000000000000 : ℚ) : ℝ) ≤ stT318 185 := by
  have hc : ((-66299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9748803857/1000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-66299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c186 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-962053/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -895383/1250000) (δ := 4001/250000000) (ψ := -195723/500000) 318 265
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t186 : ((-176371304277/2500000000000 : ℚ) : ℝ) ≤ stT318 186 := by
  have hc : ((-962153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176371304277/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-962153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c187 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((399239/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1450137/5000000) (δ := 4001/250000000) (ψ := -195723/500000) 318 265
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t187 : ((36484896851/1250000000000 : ℚ) : ℝ) ≤ stT318 187 := by
  have hc : ((399139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36484896851/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((399139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c188 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((42991/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1339699/10000000) (δ := 15999/1000000000) (ψ := -195723/500000) 318 265
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t188 : ((3918840183/62500000000 : ℚ) : ℝ) ≤ stT318 188 := by
  have hc : ((21493/25000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3918840183/62500000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((21493/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c189 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-606861/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2778627/5000000) (δ := 4001/250000000) (ψ := -195723/500000) 318 265
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t189 : ((-441499182673/10000000000000 : ℚ) : ℝ) ≤ stT318 189 := by
  have hc : ((-606961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-441499182673/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-606961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c190 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-725253/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1191099/2000000) (δ := 4023/250000000) (ψ := -195723/500000) 318 266
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t190 : ((-526226918381/10000000000000 : ℚ) : ℝ) ≤ stT318 190 := by
  have hc : ((-725353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-526226918381/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-725353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c191 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((189119/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -891111/5000000) (δ := 4023/250000000) (ψ := -195723/500000) 318 266
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t191 : ((34205875489/625000000000 : ℚ) : ℝ) ≤ stT318 191 := by
  have hc : ((94547/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34205875489/625000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((94547/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c192 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((145893/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2369189/10000000) (δ := 15911/1000000000) (ψ := -195723/500000) 318 266
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t192 : ((26317759829/625000000000 : ℚ) : ℝ) ≤ stT318 192 := by
  have hc : ((36467/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26317759829/625000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((36467/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c193 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-428347/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1299811/2000000) (δ := 15911/1000000000) (ψ := -195723/500000) 318 266
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t193 : ((-38545876869/625000000000 : ℚ) : ℝ) ≤ stT318 193 := by
  have hc : ((-428397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38545876869/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-428397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c194 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-4523/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1275087/2500000) (δ := 8009/500000000) (ψ := -195723/500000) 318 267
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t194 : ((-812011629/25000000000 : ℚ) : ℝ) ≤ stT318 194 := by
  have hc : ((-1131/2500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-812011629/25000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-1131/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c195 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((459517/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -202587/2000000) (δ := 8009/500000000) (ψ := -195723/500000) 318 267
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t195 : ((164515375619/2500000000000 : ℚ) : ℝ) ≤ stT318 195 := by
  have hc : ((459467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164515375619/2500000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((459467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c196 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((68461/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3053569/10000000) (δ := 3197/200000000) (ψ := -195723/500000) 318 267
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t196 : ((9777275937/400000000000 : ℚ) : ℝ) ≤ stT318 196 := by
  have hc : ((68441/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9777275937/400000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((68441/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c197 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-477397/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1774851/2500000) (δ := 8009/500000000) (ψ := -195723/500000) 318 267
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t197 : ((-340167141537/5000000000000 : ℚ) : ℝ) ≤ stT318 197 := by
  have hc : ((-477447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-340167141537/5000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-477447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c198 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-129747/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1145809/2500000) (δ := 7963/500000000) (ψ := -195723/500000) 318 268
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t198 : ((-9224283399/500000000000 : ℚ) : ℝ) ≤ stT318 198 := by
  have hc : ((-129797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9224283399/500000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-129797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c199 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((7787/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115637/2000000) (δ := 7963/500000000) (ψ := -195723/500000) 318 268
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t199 : ((27597446211/400000000000 : ℚ) : ℝ) ≤ stT318 199 := by
  have hc : ((38931/40000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27597446211/400000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((38931/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c200 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((206597/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 106461/312500) (δ := 16077/1000000000) (ψ := -195723/500000) 318 268
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t200 : ((73007633841/5000000000000 : ℚ) : ℝ) ≤ stT318 200 := by
  have hc : ((206497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73007633841/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((206497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c201 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-196293/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3685947/5000000) (δ := 16077/1000000000) (ψ := -195723/500000) 318 268
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t201 : ((-69234294649/1000000000000 : ℚ) : ℝ) ≤ stT318 201 := by
  have hc : ((-196313/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69234294649/1000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-196313/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c202 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-184431/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2195361/5000000) (δ := 16033/1000000000) (ψ := -195723/500000) 318 269
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t202 : ((-64917821269/5000000000000 : ℚ) : ℝ) ≤ stT318 202 := by
  have hc : ((-184531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64917821269/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-184531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c203 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((982769/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232387/5000000) (δ := 1597/100000000) (ψ := -195723/500000) 318 269
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t203 : ((344849014839/5000000000000 : ℚ) : ℝ) ≤ stT318 203 := by
  have hc : ((982669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((344849014839/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((982669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c204 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((96419/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 53779/156250) (δ := 1597/100000000) (ψ := -195723/500000) 318 269
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t204 : ((3373589583/250000000000 : ℚ) : ℝ) ≤ stT318 204 := by
  have hc : ((96369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3373589583/250000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((96369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c205 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-489033/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3664703/5000000) (δ := 1597/100000000) (ψ := -195723/500000) 318 269
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t205 : ((-341590728773/5000000000000 : ℚ) : ℝ) ≤ stT318 205 := by
  have hc : ((-489083/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-341590728773/5000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-489083/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c206 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-57767/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -563741/1250000) (δ := 797/50000000) (ψ := -195723/500000) 318 270
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t206 : ((-314575401/19531250000 : ℚ) : ℝ) ≤ stT318 206 := by
  have hc : ((-3612/15625 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-314575401/19531250000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-3612/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c207 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((241337/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -660061/10000000) (δ := 797/50000000) (ψ := -195723/500000) 318 270
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t207 : ((655169621/9765625000 : ℚ) : ℝ) ≤ stT318 207 := by
  have hc : ((15082/15625 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((655169621/9765625000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((15082/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c208 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((297701/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1585641/5000000) (δ := 16063/1000000000) (ψ := -195723/500000) 318 270
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t208 : ((1650792747/80000000000 : ℚ) : ℝ) ≤ stT318 208 := by
  have hc : ((297601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1650792747/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((297601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c209 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-188019/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6984261/10000000) (δ := 16063/1000000000) (ψ := -195723/500000) 318 270
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t209 : ((-26013879377/400000000000 : ℚ) : ℝ) ≤ stT318 209 := by
  have hc : ((-188039/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26013879377/400000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-188039/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c210 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-97533/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -154029/312500) (δ := 16047/1000000000) (ψ := -195723/500000) 318 271
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t210 : ((-16830364707/625000000000 : ℚ) : ℝ) ≤ stT318 210 := by
  have hc : ((-48779/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16830364707/625000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-48779/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c211 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((895661/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1152201/10000000) (δ := 16047/1000000000) (ψ := -195723/500000) 318 271
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t211 : ((154132317027/2500000000000 : ℚ) : ℝ) ≤ stT318 211 := by
  have hc : ((895561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154132317027/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((895561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c212 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((503929/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1303319/5000000) (δ := 3989/250000000) (ψ := -195723/500000) 318 271
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t212 : ((173015382429/5000000000000 : ℚ) : ℝ) ≤ stT318 212 := by
  have hc : ((503829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173015382429/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((503829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c213 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-102993/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6347829/10000000) (δ := 16047/1000000000) (ψ := -195723/500000) 318 271
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t213 : ((-141156471079/2500000000000 : ℚ) : ℝ) ≤ stT318 213 := by
  have hc : ((-206011/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141156471079/2500000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-206011/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c214 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-315863/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2818217/5000000) (δ := 7977/500000000) (ψ := -195723/500000) 318 272
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t214 : ((-107976852009/2500000000000 : ℚ) : ℝ) ≤ stT318 214 := by
  have hc : ((-315913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107976852009/2500000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-315913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c215 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((716477/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -60317/312500) (δ := 7977/500000000) (ψ := -195723/500000) 318 272
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t215 : ((244282407869/5000000000000 : ℚ) : ℝ) ≤ stT318 215 := by
  have hc : ((716377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((244282407869/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((716377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c216 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((30501/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 879487/5000000) (δ := 7977/500000000) (ψ := -195723/500000) 318 272
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t216 : ((20750555261/400000000000 : ℚ) : ℝ) ≤ stT318 216 := by
  have hc : ((30497/40000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20750555261/400000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((30497/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c217 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-113193/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5430999/10000000) (δ := 16049/1000000000) (ψ := -195723/500000) 318 272
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t217 : ((-15370815797/400000000000 : ℚ) : ℝ) ≤ stT318 217 := by
  have hc : ((-113213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15370815797/400000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-113213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c218 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-55061/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -206931/312500) (δ := 8031/500000000) (ψ := -195723/500000) 318 273
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t218 : ((-74592554967/1250000000000 : ℚ) : ℝ) ≤ stT318 218 := by
  have hc : ((-220269/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74592554967/1250000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-220269/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c219 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((36857/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -745829/2500000) (δ := 15941/1000000000) (ψ := -195723/500000) 318 273
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t219 : ((24898881239/1000000000000 : ℚ) : ℝ) ≤ stT318 219 := by
  have hc : ((36847/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24898881239/1000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((36847/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c220 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((483779/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 127709/2000000) (δ := 15941/1000000000) (ψ := -195723/500000) 318 273
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t220 : ((326129608071/5000000000000 : ℚ) : ℝ) ≤ stT318 220 := by
  have hc : ((483729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((326129608071/5000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((483729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c221 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-31619/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4244029/10000000) (δ := 15941/1000000000) (ψ := -195723/500000) 318 273
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t221 : ((-5321516103/625000000000 : ℚ) : ℝ) ≤ stT318 221 := by
  have hc : ((-7911/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5321516103/625000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-7911/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c222 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-199993/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 489571/625000) (δ := 15941/1000000000) (ψ := -195723/500000) 318 273
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t222 : ((-134240125041/2000000000000 : ℚ) : ℝ) ≤ stT318 222 := by
  have hc : ((-200013/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134240125041/2000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-200013/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c223 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-74677/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4301779/10000000) (δ := 15969/1000000000) (ψ := -195723/500000) 318 274
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t223 : ((-1000818711/100000000000 : ℚ) : ℝ) ≤ stT318 223 := by
  have hc : ((-74727/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1000818711/100000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-74727/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c224 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((23899/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -744711/10000000) (δ := 8017/500000000) (ψ := -195723/500000) 318 274
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t224 : ((31933036329/500000000000 : ℚ) : ℝ) ≤ stT318 224 := by
  have hc : ((47793/50000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31933036329/500000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((47793/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c225 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((436929/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2796537/10000000) (δ := 8017/500000000) (ψ := -195723/500000) 318 274
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t225 : ((145609521057/5000000000000 : ℚ) : ℝ) ≤ stT318 225 := by
  have hc : ((436829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145609521057/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((436829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c226 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-409023/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1264401/2000000) (δ := 31969/1000000000) (ψ := -195723/500000) 318 274
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t226 : ((-272111677943/5000000000000 : ℚ) : ℝ) ≤ stT318 226 := by
  have hc : ((-409073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272111677943/5000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-409073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c227 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-175749/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2937997/5000000) (δ := 15927/1000000000) (ψ := -195723/500000) 318 275
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t227 : ((-14583177797/312500000000 : ℚ) : ℝ) ≤ stT318 227 := by
  have hc : ((-87887/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14583177797/312500000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-87887/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c228 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((579569/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -595373/2500000) (δ := 15927/1000000000) (ψ := -195723/500000) 318 275
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t228 : ((191881308377/5000000000000 : ℚ) : ℝ) ≤ stT318 228 := by
  have hc : ((579469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191881308377/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((579469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c229 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((181027/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 548873/5000000) (δ := 15927/1000000000) (ψ := -195723/500000) 318 275
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t229 : ((59806341863/1000000000000 : ℚ) : ℝ) ≤ stT318 229 := by
  have hc : ((181007/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59806341863/1000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((181007/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c230 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-62801/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 22809/50000) (δ := 4019/250000000) (ψ := -195723/500000) 318 275
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t230 : ((-20713135353/1250000000000 : ℚ) : ℝ) ≤ stT318 230 := by
  have hc : ((-31413/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20713135353/1250000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-31413/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c231 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-998033/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -481071/625000) (δ := 801/50000000) (ψ := -195723/500000) 318 276
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t231 : ((-20522612613/312500000000 : ℚ) : ℝ) ≤ stT318 231 := by
  have hc : ((-998133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20522612613/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-998133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c232 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-134021/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2131527/5000000) (δ := 801/50000000) (ψ := -195723/500000) 318 276
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t232 : ((-88054862493/10000000000000 : ℚ) : ℝ) ≤ stT318 232 := by
  have hc : ((-134121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88054862493/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-134121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c233 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((188719/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -843679/10000000) (δ := 15983/1000000000) (ψ := -195723/500000) 318 276
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t233 : ((123620677579/2000000000000 : ℚ) : ℝ) ≤ stT318 233 := by
  have hc : ((188699/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123620677579/2000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((188699/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c234 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((519589/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2561067/10000000) (δ := 801/50000000) (ψ := -195723/500000) 318 276
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t234 : ((8490008727/250000000000 : ℚ) : ℝ) ≤ stT318 234 := by
  have hc : ((519489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8490008727/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((519489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c235 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-724087/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1190253/2000000) (δ := 801/50000000) (ψ := -195723/500000) 318 276
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t235 : ((-472408181523/10000000000000 : ℚ) : ℝ) ≤ stT318 235 := by
  have hc : ((-724187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-472408181523/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-724187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c236 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-166273/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6380889/10000000) (δ := 1609/100000000) (ψ := -195723/500000) 318 277
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t236 : ((-21649519377/400000000000 : ℚ) : ℝ) ≤ stT318 236 := by
  have hc : ((-166293/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21649519377/400000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-166293/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c237 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((177559/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3019391/10000000) (δ := 15913/1000000000) (ψ := -195723/500000) 318 277
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t237 : ((115304343621/5000000000000 : ℚ) : ℝ) ≤ stT318 237 := by
  have hc : ((177509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115304343621/5000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((177509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c238 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((61963/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 327957/10000000) (δ := 1609/100000000) (ψ := -195723/500000) 318 277
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t238 : ((160642204881/2500000000000 : ℚ) : ℝ) ≤ stT318 238 := by
  have hc : ((247827/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160642204881/2500000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((247827/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c239 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((13259/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 28604/78125) (δ := 15913/1000000000) (ψ := -195723/500000) 318 277
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t239 : ((8568445539/1250000000000 : ℚ) : ℝ) ≤ stT318 239 := by
  have hc : ((26493/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8568445539/1250000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((26493/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c240 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-29363/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1396151/2000000) (δ := 15913/1000000000) (ψ := -195723/500000) 318 277
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t240 : ((-75823099821/1250000000000 : ℚ) : ℝ) ≤ stT318 240 := by
  have hc : ((-234929/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75823099821/1250000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-234929/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c241 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-562861/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2710799/5000000) (δ := 15997/1000000000) (ψ := -195723/500000) 318 278
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t241 : ((-362635268877/10000000000000 : ℚ) : ℝ) ≤ stT318 241 := by
  have hc : ((-562961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-362635268877/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-562961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c242 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((658581/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1064831/5000000) (δ := 15997/1000000000) (ψ := -195723/500000) 318 278
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t242 : ((52910923793/1250000000000 : ℚ) : ℝ) ≤ stT318 242 := by
  have hc : ((658481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52910923793/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((658481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c243 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((896287/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1148679/10000000) (δ := 8003/500000000) (ψ := -195723/500000) 318 278
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t243 : ((1149807921/20000000000 : ℚ) : ℝ) ≤ stT318 243 := by
  have hc : ((896187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1149807921/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((896187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c244 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-193411/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 882717/2000000) (δ := 8003/500000000) (ψ := -195723/500000) 318 278
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t244 : ((-24776567907/2000000000000 : ℚ) : ℝ) ≤ stT318 244 := by
  have hc : ((-193511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24776567907/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-193511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c245 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-997147/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 958137/1250000) (δ := 31997/1000000000) (ψ := -195723/500000) 318 278
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t245 : ((-637118171619/10000000000000 : ℚ) : ℝ) ≤ stT318 245 := by
  have hc : ((-997247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-637118171619/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-997247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c246 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-343861/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -960911/2000000) (δ := 8049/500000000) (ψ := -195723/500000) 318 279
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t246 : ((-219301622497/10000000000000 : ℚ) : ℝ) ≤ stT318 246 := by
  have hc : ((-343961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219301622497/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-343961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c247 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((80699/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1579399/10000000) (δ := 8049/500000000) (ψ := -195723/500000) 318 279
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t247 : ((12835279919/250000000000 : ℚ) : ℝ) ≤ stT318 247 := by
  have hc : ((80689/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12835279919/250000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((80689/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c248 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((794211/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1632719/10000000) (δ := 8049/500000000) (ψ := -195723/500000) 318 279
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t248 : ((100852097/2000000000 : ℚ) : ℝ) ≤ stT318 248 := by
  have hc : ((794111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100852097/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((794111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c249 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-354103/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4831879/10000000) (δ := 3181/200000000) (ψ := -195723/500000) 318 279
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t249 : ((-8978691847/400000000000 : ℚ) : ℝ) ≤ stT318 249 := by
  have hc : ((-354203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8978691847/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-354203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c250 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-12473/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1537929/2000000) (δ := 15991/1000000000) (ψ := -195723/500000) 318 280
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t250 : ((-3944707129/62500000000 : ℚ) : ℝ) ≤ stT318 250 := by
  have hc : ((-49897/50000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3944707129/62500000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-49897/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c251 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-29179/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -903201/2000000) (δ := 15991/1000000000) (ψ := -195723/500000) 318 280
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t251 : ((-7370211537/500000000000 : ℚ) : ℝ) ≤ stT318 251 := by
  have hc : ((-58383/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).2
  have h0 : (0:ℝ) ≤ ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7370211537/500000000000 : ℚ) : ℝ)
      = ((126239/2000000 : ℚ) : ℝ) * ((-58383/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c252 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((428339/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -271001/2000000) (δ := 4003/250000000) (ψ := -195723/500000) 318 280
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t252 : ((13489818633/250000000000 : ℚ) : ℝ) ≤ stT318 252 := by
  have hc : ((428289/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).1
  have hw2 : ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31497/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13489818633/250000000000 : ℚ) : ℝ)
      = ((31497/500000 : ℚ) : ℝ) * ((428289/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c253 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((376757/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1793513/10000000) (δ := 4003/250000000) (ψ := -195723/500000) 318 280
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t253 : ((118416715329/2500000000000 : ℚ) : ℝ) ≤ stT318 253 := by
  have hc : ((376707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).1
  have hw2 : ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((314347/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118416715329/2500000000000 : ℚ) : ℝ)
      = ((314347/5000000 : ℚ) : ℝ) * ((376707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c254 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-39039/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4929629/10000000) (δ := 4003/250000000) (ψ := -195723/500000) 318 280
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t254 : ((-95709099/3906250000 : ℚ) : ℝ) ≤ stT318 254 := by
  have hc : ((-39049/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95709099/3906250000 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-39049/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c255 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-49841/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7654541/10000000) (δ := 15919/1000000000) (ψ := -195723/500000) 318 281
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t255 : ((-624296227/10000000000 : ℚ) : ℝ) ≤ stT318 255 := by
  have hc : ((-24923/25000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-624296227/10000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-24923/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c256 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-121957/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4542991/10000000) (δ := 4021/250000000) (ψ := -195723/500000) 318 281
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t256 : ((-76254497007/5000000000000 : ℚ) : ℝ) ≤ stT318 256 := by
  have hc : ((-122007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).2
  have h0 : (0:ℝ) ≤ ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76254497007/5000000000000 : ℚ) : ℝ)
      = ((625001/10000000 : ℚ) : ℝ) * ((-122007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c257 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((418931/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -360901/2500000) (δ := 4021/250000000) (ψ := -195723/500000) 318 281
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t257 : ((130645213971/2500000000000 : ℚ) : ℝ) ≤ stT318 257 := by
  have hc : ((418881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130645213971/2500000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((418881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c258 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((158303/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1643779/10000000) (δ := 15919/1000000000) (ψ := -195723/500000) 318 281
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t258 : ((24635640969/500000000000 : ℚ) : ℝ) ≤ stT318 258 := by
  have hc : ((158283/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24635640969/500000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((158283/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c259 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-311621/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1179809/2500000) (δ := 4021/250000000) (ψ := -195723/500000) 318 281
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t259 : ((-19369407777/1000000000000 : ℚ) : ℝ) ≤ stT318 259 := by
  have hc : ((-311721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19369407777/1000000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-311721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c260 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-199919/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 121607/156250) (δ := 4021/250000000) (ψ := -195723/500000) 318 281
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t260 : ((-61998484693/1000000000000 : ℚ) : ℝ) ≤ stT318 260 := by
  have hc : ((-199939/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61998484693/1000000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-199939/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c261 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-184769/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4873269/10000000) (δ := 15977/1000000000) (ψ := -195723/500000) 318 282
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t261 : ((-22880037743/1000000000000 : ℚ) : ℝ) ≤ stT318 261 := by
  have hc : ((-184819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22880037743/1000000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-184819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c262 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((743007/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1833109/10000000) (δ := 23913/500000000) (ψ := -195723/500000) 318 282
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t262 : ((229484715207/5000000000000 : ℚ) : ℝ) ≤ stT318 262 := by
  have hc : ((742907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).1
  have hw2 : ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229484715207/5000000000000 : ℚ) : ℝ)
      = ((308901/5000000 : ℚ) : ℝ) * ((742907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c263 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((177567/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1195443/10000000) (δ := 15977/1000000000) (ψ := -195723/500000) 318 282
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t263 : ((54740048211/1000000000000 : ℚ) : ℝ) ≤ stT318 263 := by
  have hc : ((177547/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54740048211/1000000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((177547/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c264 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-4559/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1053137/2500000) (δ := 23913/500000000) (ψ := -195723/500000) 318 282
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t264 : ((-1404167427/200000000000 : ℚ) : ℝ) ≤ stT318 264 := by
  have hc : ((-4563/40000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).2
  have h0 : (0:ℝ) ≤ ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1404167427/200000000000 : ℚ) : ℝ)
      = ((307729/5000000 : ℚ) : ℝ) * ((-4563/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c265 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-967837/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1804551/2500000) (δ := 15977/1000000000) (ψ := -195723/500000) 318 282
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t265 : ((-74324978419/1250000000000 : ℚ) : ℝ) ≤ stT318 265 := by
  have hc : ((-967937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).2
  have h0 : (0:ℝ) ≤ ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74324978419/1250000000000 : ℚ) : ℝ)
      = ((76787/1250000 : ℚ) : ℝ) * ((-967937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c266 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-58701/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -171731/312500) (δ := 1607/100000000) (ψ := -195723/500000) 318 283
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t266 : ((-1799903127/50000000000 : ℚ) : ℝ) ≤ stT318 266 := by
  have hc : ((-58711/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1799903127/50000000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-58711/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c267 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((536151/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2512313/10000000) (δ := 15933/1000000000) (ψ := -195723/500000) 318 283
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t267 : ((32805785149/1000000000000 : ℚ) : ℝ) ≤ stT318 267 := by
  have hc : ((536051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).1
  have hw2 : ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61199/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32805785149/1000000000000 : ℚ) : ℝ)
      = ((61199/1000000 : ℚ) : ℝ) * ((536051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c268 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((491573/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 91927/2000000) (δ := 1607/100000000) (ψ := -195723/500000) 318 283
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t268 : ((300245349981/5000000000000 : ℚ) : ℝ) ≤ stT318 268 := by
  have hc : ((491523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).1
  have hw2 : ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((300245349981/5000000000000 : ℚ) : ℝ)
      = ((610847/10000000 : ℚ) : ℝ) * ((491523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c269 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((503/2500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3420533/10000000) (δ := 1607/100000000) (ψ := -195723/500000) 318 283
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t269 : ((122612681/10000000000 : ℚ) : ℝ) ≤ stT318 269 := by
  have hc : ((2011/10000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122612681/10000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((2011/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c270 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-829039/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 318523/500000) (δ := 1607/100000000) (ψ := -195723/500000) 318 283
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t270 : ((-504598241759/10000000000000 : ℚ) : ℝ) ≤ stT318 270 := by
  have hc : ((-829139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).2
  have h0 : (0:ℝ) ≤ ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-504598241759/10000000000000 : ℚ) : ℝ)
      = ((608581/10000000 : ℚ) : ℝ) * ((-829139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c271 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-208813/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6398467/10000000) (δ := 16041/1000000000) (ψ := -195723/500000) 318 284
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t271 : ((-63430052483/1250000000000 : ℚ) : ℝ) ≤ stT318 271 := by
  have hc : ((-104419/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).2
  have h0 : (0:ℝ) ≤ ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63430052483/1250000000000 : ℚ) : ℝ)
      = ((607457/10000000 : ℚ) : ℝ) * ((-104419/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c272 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((181653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3470323/10000000) (δ := 16041/1000000000) (ψ := -195723/500000) 318 284
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t272 : ((110082664467/10000000000000 : ℚ) : ℝ) ≤ stT318 272 := by
  have hc : ((181553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110082664467/10000000000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((181553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c273 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((975643/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -34557/625000) (δ := 7981/500000000) (ψ := -195723/500000) 318 284
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t273 : ((590424963261/10000000000000 : ℚ) : ℝ) ≤ stT318 273 := by
  have hc : ((975543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).1
  have hw2 : ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((605227/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((590424963261/10000000000000 : ℚ) : ℝ)
      = ((605227/10000000 : ℚ) : ℝ) * ((975543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c274 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((588519/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1176963/5000000) (δ := 7981/500000000) (ψ := -195723/500000) 318 284
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t274 : ((177738431559/5000000000000 : ℚ) : ℝ) ≤ stT318 274 := by
  have hc : ((588419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).1
  have hw2 : ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((302061/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177738431559/5000000000000 : ℚ) : ℝ)
      = ((302061/5000000 : ℚ) : ℝ) * ((588419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c275 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-504857/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 328127/625000) (δ := 16041/1000000000) (ψ := -195723/500000) 318 284
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t275 : ((-304500685011/10000000000000 : ℚ) : ℝ) ≤ stT318 275 := by
  have hc : ((-504957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-304500685011/10000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-504957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c276 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-124207/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7572241/10000000) (δ := 3211/200000000) (ψ := -195723/500000) 318 285
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t276 : ((-14954288727/250000000000 : ℚ) : ℝ) ≤ stT318 276 := by
  have hc : ((-248439/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).2
  have h0 : (0:ℝ) ≤ ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14954288727/250000000000 : ℚ) : ℝ)
      = ((60193/1000000 : ℚ) : ℝ) * ((-248439/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c277 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-303143/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1174241/2500000) (δ := 3987/250000000) (ψ := -195723/500000) 318 285
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t277 : ((-91100565303/5000000000000 : ℚ) : ℝ) ≤ stT318 277 := by
  have hc : ((-303243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).2
  have h0 : (0:ℝ) ≤ ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91100565303/5000000000000 : ℚ) : ℝ)
      = ((300421/5000000 : ℚ) : ℝ) * ((-303243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c278 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((743277/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -916051/5000000) (δ := 3987/250000000) (ψ := -195723/500000) 318 285
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t278 : ((5571597969/125000000000 : ℚ) : ℝ) ≤ stT318 278 := by
  have hc : ((743177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5571597969/125000000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((743177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c279 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((917531/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40897/400000) (δ := 3987/250000000) (ψ := -195723/500000) 318 285
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t279 : ((137312815201/2500000000000 : ℚ) : ℝ) ≤ stT318 279 := by
  have hc : ((917431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).1
  have hw2 : ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149671/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137312815201/2500000000000 : ℚ) : ℝ)
      = ((149671/2500000 : ℚ) : ℝ) * ((917431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c280 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((6013/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 773371/2000000) (δ := 3211/200000000) (ψ := -195723/500000) 318 285
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t280 : ((447314079/312500000000 : ℚ) : ℝ) ≤ stT318 280 := by
  have hc : ((1497/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).1
  have hw2 : ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((447314079/312500000000 : ℚ) : ℝ)
      = ((298807/5000000 : ℚ) : ℝ) * ((1497/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c281 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-111941/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 670103/1000000) (δ := 3211/200000000) (ψ := -195723/500000) 318 285
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t281 : ((-2671434417/50000000000 : ℚ) : ℝ) ≤ stT318 281 := by
  have hc : ((-223907/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2671434417/50000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-223907/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c282 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-784763/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -247311/400000) (δ := 3987/250000000) (ψ := -195723/500000) 318 286
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t282 : ((-116844909399/2500000000000 : ℚ) : ℝ) ≤ stT318 282 := by
  have hc : ((-784863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).2
  have h0 : (0:ℝ) ≤ ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116844909399/2500000000000 : ℚ) : ℝ)
      = ((148873/2500000 : ℚ) : ℝ) * ((-784863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c283 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((221491/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1684317/5000000) (δ := 3987/250000000) (ψ := -195723/500000) 318 286
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t283 : ((65801611629/5000000000000 : ℚ) : ℝ) ≤ stT318 283 := by
  have hc : ((221391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65801611629/5000000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((221391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c284 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((974629/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -564351/10000000) (δ := 3987/250000000) (ψ := -195723/500000) 318 286
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t284 : ((57827576331/1000000000000 : ℚ) : ℝ) ≤ stT318 284 := by
  have hc : ((974529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57827576331/1000000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((974529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c285 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((313929/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 445999/2000000) (δ := 3211/200000000) (ψ := -195723/500000) 318 286
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t285 : ((46481399473/1250000000000 : ℚ) : ℝ) ≤ stT318 285 := by
  have hc : ((313879/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).1
  have hw2 : ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((148087/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46481399473/1250000000000 : ℚ) : ℝ)
      = ((148087/2500000 : ℚ) : ℝ) * ((313879/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c286 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-84293/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5014641/10000000) (δ := 3987/250000000) (ψ := -195723/500000) 318 286
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t286 : ((-49855372969/2000000000000 : ℚ) : ℝ) ≤ stT318 286 := by
  have hc : ((-84313/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49855372969/2000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-84313/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c287 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-999667/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7789509/10000000) (δ := 3987/250000000) (ψ := -195723/500000) 318 286
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t287 : ((-295072232147/5000000000000 : ℚ) : ℝ) ≤ stT318 287 := by
  have hc : ((-999767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-295072232147/5000000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-999767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c288 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-471083/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1030657/2000000) (δ := 7981/500000000) (ψ := -195723/500000) 318 287
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t288 : ((-34705926231/1250000000000 : ℚ) : ℝ) ≤ stT318 288 := by
  have hc : ((-471183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).2
  have h0 : (0:ℝ) ≤ ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34705926231/1250000000000 : ℚ) : ℝ)
      = ((73657/1250000 : ℚ) : ℝ) * ((-471183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c289 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((35893/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -299707/1250000) (δ := 7981/500000000) (ψ := -195723/500000) 318 287
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t289 : ((16887873909/500000000000 : ℚ) : ℝ) ≤ stT318 289 := by
  have hc : ((143547/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16887873909/500000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((143547/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c290 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((990299/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10891/312500) (δ := 16041/1000000000) (ψ := -195723/500000) 318 287
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t290 : ((29073232839/500000000000 : ℚ) : ℝ) ≤ stT318 290 := by
  have hc : ((990199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29073232839/500000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((990199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c291 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((82603/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3085141/10000000) (δ := 7981/500000000) (ψ := -195723/500000) 318 287
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t291 : ((2420402469/125000000000 : ℚ) : ℝ) ≤ stT318 291 := by
  have hc : ((41289/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2420402469/125000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((41289/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c292 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-684699/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1453117/2500000) (δ := 7981/500000000) (ψ := -195723/500000) 318 287
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t292 : ((-200374241797/5000000000000 : ℚ) : ℝ) ≤ stT318 292 := by
  have hc : ((-684799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200374241797/5000000000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-684799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c293 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-481809/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7177549/10000000) (δ := 16069/1000000000) (ψ := -195723/500000) 318 288
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t293 : ((-281505400813/5000000000000 : ℚ) : ℝ) ≤ stT318 293 := by
  have hc : ((-481859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-281505400813/5000000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-481859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c294 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-6721/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -893781/2000000) (δ := 7967/500000000) (ψ := -195723/500000) 318 288
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t294 : ((-7843180779/625000000000 : ℚ) : ℝ) ≤ stT318 294 := by
  have hc : ((-53793/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7843180779/625000000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-53793/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c295 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((759819/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1769403/10000000) (δ := 7967/500000000) (ψ := -195723/500000) 318 288
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t295 : ((221162557809/5000000000000 : ℚ) : ℝ) ≤ stT318 295 := by
  have hc : ((759719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).1
  have hw2 : ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((291111/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221162557809/5000000000000 : ℚ) : ℝ)
      = ((291111/5000000 : ℚ) : ℝ) * ((759719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c296 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((932911/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 920957/10000000) (δ := 16069/1000000000) (ψ := -195723/500000) 318 288
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t296 : ((271092600009/5000000000000 : ℚ) : ℝ) ≤ stT318 296 := by
  have hc : ((932811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).1
  have hw2 : ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((271092600009/5000000000000 : ℚ) : ℝ)
      = ((290619/5000000 : ℚ) : ℝ) * ((932811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c297 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((12953/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3602253/10000000) (δ := 7967/500000000) (ψ := -195723/500000) 318 288
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t297 : ((3755139647/500000000000 : ℚ) : ℝ) ≤ stT318 297 := by
  have hc : ((12943/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).1
  have hw2 : ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290129/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3755139647/500000000000 : ℚ) : ℝ)
      = ((290129/5000000 : ℚ) : ℝ) * ((12943/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c298 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-806967/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6274487/10000000) (δ := 16069/1000000000) (ψ := -195723/500000) 318 288
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t298 : ((-93504361419/2000000000000 : ℚ) : ℝ) ≤ stT318 298 := by
  have hc : ((-807067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).2
  have h0 : (0:ℝ) ≤ ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93504361419/2000000000000 : ℚ) : ℝ)
      = ((115857/2000000 : ℚ) : ℝ) * ((-807067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c299 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-907487/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6770147/10000000) (δ := 1997/125000000) (ψ := -195723/500000) 318 289
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t299 : ((-104974235181/2000000000000 : ℚ) : ℝ) ≤ stT318 299 := by
  have hc : ((-907587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).2
  have h0 : (0:ℝ) ≤ ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104974235181/2000000000000 : ℚ) : ℝ)
      = ((115663/2000000 : ℚ) : ℝ) * ((-907587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c300 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-75421/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2057861/5000000) (δ := 16027/1000000000) (ψ := -195723/500000) 318 289
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t300 : ((-43602124871/10000000000000 : ℚ) : ℝ) ≤ stT318 300 := by
  have hc : ((-75521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).2
  have h0 : (0:ℝ) ≤ ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43602124871/10000000000000 : ℚ) : ℝ)
      = ((577351/10000000 : ℚ) : ℝ) * ((-75521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c301 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((33281/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1470121/10000000) (δ := 16027/1000000000) (ψ := -195723/500000) 318 289
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t301 : ((1918053003/40000000000 : ℚ) : ℝ) ≤ stT318 301 := by
  have hc : ((33277/40000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1918053003/40000000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((33277/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c302 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((893061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 233347/2000000) (δ := 16027/1000000000) (ψ := -195723/500000) 318 289
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t302 : ((102768202607/2000000000000 : ℚ) : ℝ) ≤ stT318 302 := by
  have hc : ((892961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).1
  have hw2 : ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((115087/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102768202607/2000000000000 : ℚ) : ℝ)
      = ((115087/2000000 : ℚ) : ℝ) * ((892961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c303 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((52833/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1897423/5000000) (δ := 16027/1000000000) (ψ := -195723/500000) 318 289
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t303 : ((7573566193/2500000000000 : ℚ) : ℝ) ≤ stT318 303 := by
  have hc : ((52733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).1
  have hw2 : ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143621/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7573566193/2500000000000 : ℚ) : ℝ)
      = ((143621/2500000 : ℚ) : ℝ) * ((52733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c304 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-209679/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1603573/2500000) (δ := 1997/125000000) (ψ := -195723/500000) 318 289
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t304 : ((-751710201/15625000000 : ℚ) : ℝ) ≤ stT318 304 := by
  have hc : ((-26213/31250 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-751710201/15625000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-26213/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c305 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-35691/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6682891/10000000) (δ := 4021/250000000) (ψ := -195723/500000) 318 290
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t305 : ((-4087784261/80000000000 : ℚ) : ℝ) ≤ stT318 305 := by
  have hc : ((-7139/8000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).2
  have h0 : (0:ℝ) ≤ ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4087784261/80000000000 : ℚ) : ℝ)
      = ((572599/10000000 : ℚ) : ℝ) * ((-7139/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c306 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-3069/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2040269/5000000) (δ := 4021/250000000) (ψ := -195723/500000) 318 290
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t306 : ((-439322247/125000000000 : ℚ) : ℝ) ≤ stT318 306 := by
  have hc : ((-1537/25000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).2
  have h0 : (0:ℝ) ≤ ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-439322247/125000000000 : ℚ) : ℝ)
      = ((285831/5000000 : ℚ) : ℝ) * ((-1537/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c307 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((103539/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1486771/10000000) (δ := 4021/250000000) (ψ := -195723/500000) 318 290
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t307 : ((11817135869/250000000000 : ℚ) : ℝ) ≤ stT318 307 := by
  have hc : ((207053/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11817135869/250000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((207053/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c308 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((180999/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1098569/10000000) (δ := 4021/250000000) (ψ := -195723/500000) 318 290
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t308 : ((51561098079/1000000000000 : ℚ) : ℝ) ≤ stT318 308 := by
  have hc : ((180979/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51561098079/1000000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((180979/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c309 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((50201/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3675561/10000000) (δ := 15919/1000000000) (ψ := -195723/500000) 318 290
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t309 : ((356623761/62500000000 : ℚ) : ℝ) ≤ stT318 309 := by
  have hc : ((50151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((356623761/62500000000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((50151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c310 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-399877/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3122103/5000000) (δ := 15919/1000000000) (ψ := -195723/500000) 318 290
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t310 : ((-113571669387/2500000000000 : ℚ) : ℝ) ≤ stT318 310 := by
  have hc : ((-399927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113571669387/2500000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-399927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c311 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-232141/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6903301/10000000) (δ := 4003/250000000) (ψ := -195723/500000) 318 291
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t311 : ((-8228079123/156250000000 : ℚ) : ℝ) ≤ stT318 311 := by
  have hc : ((-116083/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8228079123/156250000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-116083/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c312 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-168867/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -543899/1250000) (δ := 4003/250000000) (ψ := -195723/500000) 318 291
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t312 : ((-95658808413/10000000000000 : ℚ) : ℝ) ≤ stT318 312 := by
  have hc : ((-168967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95658808413/10000000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-168967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c313 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((374953/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -225899/1250000) (δ := 4003/250000000) (ψ := -195723/500000) 318 291
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t313 : ((211907547399/5000000000000 : ℚ) : ℝ) ≤ stT318 313 := by
  have hc : ((374903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).1
  have hw2 : ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((565233/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211907547399/5000000000000 : ℚ) : ℝ)
      = ((565233/10000000 : ℚ) : ℝ) * ((374903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c314 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((47891/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 728699/10000000) (δ := 4003/250000000) (ψ := -195723/500000) 318 291
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t314 : ((3377950269/62500000000 : ℚ) : ℝ) ≤ stT318 314 := by
  have hc : ((23943/25000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3377950269/62500000000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((23943/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c315 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((264969/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3256561/10000000) (δ := 15991/1000000000) (ψ := -195723/500000) 318 291
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t315 : ((37309182471/2500000000000 : ℚ) : ℝ) ≤ stT318 315 := by
  have hc : ((264869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37309182471/2500000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((264869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c316 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-674111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5776393/10000000) (δ := 15991/1000000000) (ψ := -195723/500000) 318 291
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t316 : ((-23704584549/625000000000 : ℚ) : ℝ) ≤ stT318 316 := by
  have hc : ((-674211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).2
  have h0 : (0:ℝ) ≤ ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23704584549/625000000000 : ℚ) : ℝ)
      = ((35159/625000 : ℚ) : ℝ) * ((-674211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c317 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-196991/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -927471/1250000) (δ := 3181/200000000) (ψ := -195723/500000) 318 292
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t317 : ((-13831551277/250000000000 : ℚ) : ℝ) ≤ stT318 317 := by
  have hc : ((-197011/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).2
  have h0 : (0:ℝ) ≤ ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13831551277/250000000000 : ℚ) : ℝ)
      = ((70207/1250000 : ℚ) : ℝ) * ((-197011/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c318 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-77061/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1228959/2500000) (δ := 3181/200000000) (ψ := -195723/500000) 318 292
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t318 : ((-43224943613/2000000000000 : ℚ) : ℝ) ≤ stT318 318 := by
  have hc : ((-77081/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43224943613/2000000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-77081/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c319 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((567049/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -483939/2000000) (δ := 3181/200000000) (ψ := -195723/500000) 318 292
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t319 : ((79357552377/2500000000000 : ℚ) : ℝ) ≤ stT318 319 := by
  have hc : ((566949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).1
  have hw2 : ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((139973/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79357552377/2500000000000 : ℚ) : ℝ)
      = ((139973/2500000 : ℚ) : ℝ) * ((566949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c320 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((7997/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4281/625000) (δ := 3181/200000000) (ψ := -195723/500000) 318 292
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t320 : ((2793752337/50000000000 : ℚ) : ℝ) ≤ stT318 320 := by
  have hc : ((39981/40000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).1
  have hw2 : ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69877/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2793752337/50000000000 : ℚ) : ℝ)
      = ((69877/1250000 : ℚ) : ℝ) * ((39981/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c321 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((65461/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 509811/2000000) (δ := 3181/200000000) (ψ := -195723/500000) 318 292
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t321 : ((14611901213/500000000000 : ℚ) : ℝ) ≤ stT318 321 := by
  have hc : ((130897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).1
  have hw2 : ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111629/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14611901213/500000000000 : ℚ) : ℝ)
      = ((111629/2000000 : ℚ) : ℝ) * ((130897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c322 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-106017/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5021823/10000000) (δ := 3181/200000000) (ψ := -195723/500000) 318 292
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t322 : ((-29547489859/1250000000000 : ℚ) : ℝ) ≤ stT318 322 := by
  have hc : ((-53021/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).2
  have h0 : (0:ℝ) ≤ ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29547489859/1250000000000 : ℚ) : ℝ)
      = ((557279/10000000 : ℚ) : ℝ) * ((-53021/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c323 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-989243/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7486959/10000000) (δ := 3181/200000000) (ψ := -195723/500000) 318 292
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t323 : ((-110097057069/2000000000000 : ℚ) : ℝ) ≤ stT318 323 := by
  have hc : ((-989343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).2
  have h0 : (0:ℝ) ≤ ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110097057069/2000000000000 : ℚ) : ℝ)
      = ((111283/2000000 : ℚ) : ℝ) * ((-989343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c324 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-670293/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11527/20000) (δ := 3201/200000000) (ψ := -195723/500000) 318 293
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t324 : ((-93110213377/2500000000000 : ℚ) : ℝ) ≤ stT318 324 := by
  have hc : ((-670393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).2
  have h0 : (0:ℝ) ≤ ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93110213377/2500000000000 : ℚ) : ℝ)
      = ((138889/2500000 : ℚ) : ℝ) * ((-670393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c325 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((242891/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -828407/2500000) (δ := 3201/200000000) (ψ := -195723/500000) 318 293
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t325 : ((1346761677/100000000000 : ℚ) : ℝ) ≤ stT318 325 := by
  have hc : ((242791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1346761677/100000000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((242791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c326 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((939889/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -871229/10000000) (δ := 3201/200000000) (ψ := -195723/500000) 318 293
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t326 : ((65062532259/1250000000000 : ℚ) : ℝ) ≤ stT318 326 := by
  have hc : ((939789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).1
  have hw2 : ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69231/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65062532259/1250000000000 : ℚ) : ℝ)
      = ((69231/1250000 : ℚ) : ℝ) * ((939789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c327 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((810683/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1563697/10000000) (δ := 3201/200000000) (ψ := -195723/500000) 318 293
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t327 : ((448253209583/10000000000000 : ℚ) : ℝ) ≤ stT318 327 := by
  have hc : ((810583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).1
  have hw2 : ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((553001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((448253209583/10000000000000 : ℚ) : ℝ)
      = ((553001/10000000 : ℚ) : ℝ) * ((810583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c328 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-6423/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3991229/10000000) (δ := 7999/500000000) (ψ := -195723/500000) 318 293
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t328 : ((-111259837/78125000000 : ℚ) : ℝ) ≤ stT318 328 := by
  have hc : ((-403/15625 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111259837/78125000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-403/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c329 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-838061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6411289/10000000) (δ := 3201/200000000) (ψ := -195723/500000) 318 293
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t329 : ((-231046623099/5000000000000 : ℚ) : ℝ) ≤ stT318 329 := by
  have hc : ((-838161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-231046623099/5000000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-838161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c330 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-46283/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6883929/10000000) (δ := 1989/125000000) (ψ := -195723/500000) 318 294
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t330 : ((-796272213/15625000000 : ℚ) : ℝ) ≤ stT318 330 := by
  have hc : ((-2893/3125 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).2
  have h0 : (0:ℝ) ≤ ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-796272213/15625000000 : ℚ) : ℝ)
      = ((275241/5000000 : ℚ) : ℝ) * ((-2893/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c331 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-109409/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2239249/5000000) (δ := 16091/1000000000) (ψ := -195723/500000) 318 294
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t331 : ((-1203282787/100000000000 : ℚ) : ℝ) ≤ stT318 331 := by
  have hc : ((-109459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1203282787/100000000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-109459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c332 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((67331/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2080301/10000000) (δ := 16091/1000000000) (ψ := -195723/500000) 318 294
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t332 : ((36947178541/1000000000000 : ℚ) : ℝ) ≤ stT318 332 := by
  have hc : ((67321/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).1
  have hw2 : ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36947178541/1000000000000 : ℚ) : ℝ)
      = ((548821/10000000 : ℚ) : ℝ) * ((67321/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c333 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((992289/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 155331/5000000) (δ := 1989/125000000) (ψ := -195723/500000) 318 294
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t333 : ((135928900811/2500000000000 : ℚ) : ℝ) ≤ stT318 333 := by
  have hc : ((992189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135928900811/2500000000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((992189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c334 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((236639/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2694469/10000000) (δ := 16091/1000000000) (ψ := -195723/500000) 318 294
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t334 : ((5178223443/200000000000 : ℚ) : ℝ) ≤ stT318 334 := by
  have hc : ((236589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5178223443/200000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((236589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c335 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-27617/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5071201/10000000) (δ := 16091/1000000000) (ψ := -195723/500000) 318 294
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t335 : ((-60368844987/2500000000000 : ℚ) : ℝ) ≤ stT318 335 := by
  have hc : ((-110493/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).2
  have h0 : (0:ℝ) ≤ ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60368844987/2500000000000 : ℚ) : ℝ)
      = ((546359/10000000 : ℚ) : ℝ) * ((-110493/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c336 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-246593/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3720389/5000000) (δ := 16091/1000000000) (ψ := -195723/500000) 318 294
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t336 : ((-13454121681/250000000000 : ℚ) : ℝ) ≤ stT318 336 := by
  have hc : ((-123309/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).2
  have h0 : (0:ℝ) ≤ ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13454121681/250000000000 : ℚ) : ℝ)
      = ((109109/2000000 : ℚ) : ℝ) * ((-123309/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c337 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-711089/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1476151/2500000) (δ := 999/62500000) (ψ := -195723/500000) 318 295
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t337 : ((-77481907983/2000000000000 : ℚ) : ℝ) ≤ stT318 337 := by
  have hc : ((-711189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77481907983/2000000000000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-711189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c338 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((75291/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1774549/5000000) (δ := 16019/1000000000) (ψ := -195723/500000) 318 295
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t338 : ((5115710831/625000000000 : ℚ) : ℝ) ≤ stT318 338 := by
  have hc : ((75241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5115710831/625000000000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((75241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c339 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((177383/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -120043/1000000) (δ := 999/62500000) (ψ := -195723/500000) 318 295
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t339 : ((154128447/3200000000 : ℚ) : ℝ) ≤ stT318 339 := by
  have hc : ((177363/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).1
  have hw2 : ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((869/16000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154128447/3200000000 : ℚ) : ℝ)
      = ((869/16000 : ℚ) : ℝ) * ((177363/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c340 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((448801/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1141243/10000000) (δ := 16019/1000000000) (ψ := -195723/500000) 318 295
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t340 : ((121684667413/2500000000000 : ℚ) : ℝ) ≤ stT318 340 := by
  have hc : ((448751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).1
  have hw2 : ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121684667413/2500000000000 : ℚ) : ℝ)
      = ((271163/5000000 : ℚ) : ℝ) * ((448751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c341 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((8971/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3475999/10000000) (δ := 16019/1000000000) (ψ := -195723/500000) 318 295
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t341 : ((242767899/25000000000 : ℚ) : ℝ) ≤ stT318 341 := by
  have hc : ((4483/25000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).1
  have hw2 : ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((54153/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242767899/25000000000 : ℚ) : ℝ)
      = ((54153/1000000 : ℚ) : ℝ) * ((4483/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c342 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-341113/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5803997/10000000) (δ := 999/62500000) (ψ := -195723/500000) 318 295
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t342 : ((-184480139457/5000000000000 : ℚ) : ℝ) ≤ stT318 342 := by
  have hc : ((-341163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184480139457/5000000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-341163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c343 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-994123/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1516561/2000000) (δ := 4019/250000000) (ψ := -195723/500000) 318 296
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t343 : ((-10736614177/200000000000 : ℚ) : ℝ) ≤ stT318 343 := by
  have hc : ((-994223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).2
  have h0 : (0:ℝ) ≤ ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10736614177/200000000000 : ℚ) : ℝ)
      = ((10799/200000 : ℚ) : ℝ) * ((-994223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c344 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-255593/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5268401/10000000) (δ := 4019/250000000) (ψ := -195723/500000) 318 296
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t344 : ((-34458375613/1250000000000 : ℚ) : ℝ) ≤ stT318 344 := by
  have hc : ((-255643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).2
  have h0 : (0:ℝ) ≤ ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34458375613/1250000000000 : ℚ) : ℝ)
      = ((134791/2500000 : ℚ) : ℝ) * ((-255643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c345 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((376973/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -118427/400000) (δ := 4019/250000000) (ψ := -195723/500000) 318 296
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t345 : ((202901262613/10000000000000 : ℚ) : ℝ) ≤ stT318 345 := by
  have hc : ((376873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202901262613/10000000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((376873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c346 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((193077/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -329853/5000000) (δ := 15927/1000000000) (ψ := -195723/500000) 318 296
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t346 : ((103788022371/2000000000000 : ℚ) : ℝ) ≤ stT318 346 := by
  have hc : ((193057/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103788022371/2000000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((193057/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c347 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((396869/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 204333/1250000) (δ := 15927/1000000000) (ψ := -195723/500000) 318 296
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t347 : ((53255887533/1250000000000 : ℚ) : ℝ) ≤ stT318 347 := by
  have hc : ((396819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53255887533/1250000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((396819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c348 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((911/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 784487/2000000) (δ := 4019/250000000) (ψ := -195723/500000) 318 296
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t348 : ((57693027/625000000000 : ℚ) : ℝ) ≤ stT318 348 := by
  have hc : ((861/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57693027/625000000000 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((861/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c349 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-4937/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 775461/1250000) (δ := 15927/1000000000) (ψ := -195723/500000) 318 296
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t349 : ((-2643051411/62500000000 : ℚ) : ℝ) ≤ stT318 349 := by
  have hc : ((-39501/50000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).2
  have h0 : (0:ℝ) ≤ ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2643051411/62500000000 : ℚ) : ℝ)
      = ((66911/1250000 : ℚ) : ℝ) * ((-39501/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c350 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-60561/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7229621/10000000) (δ := 8017/500000000) (ψ := -195723/500000) 318 297
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t350 : ((-129498352687/2500000000000 : ℚ) : ℝ) ≤ stT318 350 := by
  have hc : ((-242269/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129498352687/2500000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-242269/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c351 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-402061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4961407/10000000) (δ := 15969/1000000000) (ψ := -195723/500000) 318 297
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t351 : ((-214657857521/10000000000000 : ℚ) : ℝ) ≤ stT318 351 := by
  have hc : ((-402161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-214657857521/10000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-402161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c352 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((47143/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2699711/10000000) (δ := 8017/500000000) (ψ := -195723/500000) 318 297
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t352 : ((25121936133/1000000000000 : ℚ) : ℝ) ≤ stT318 352 := by
  have hc : ((47133/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).1
  have hw2 : ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((533001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25121936133/1000000000000 : ℚ) : ℝ)
      = ((533001/10000000 : ℚ) : ℝ) * ((47133/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c353 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((246061/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55547/1250000) (δ := 15969/1000000000) (ψ := -195723/500000) 318 297
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t353 : ((16368959607/312500000000 : ℚ) : ℝ) ≤ stT318 353 := by
  have hc : ((61509/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).1
  have hw2 : ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((266123/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16368959607/312500000000 : ℚ) : ℝ)
      = ((266123/5000000 : ℚ) : ℝ) * ((61509/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c354 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((750591/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9023/50000) (δ := 8017/500000000) (ψ := -195723/500000) 318 297
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t354 : ((199440731777/5000000000000 : ℚ) : ℝ) ≤ stT318 354 := by
  have hc : ((750491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199440731777/5000000000000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((750491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c355 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-1201/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126473/312500) (δ := 8017/500000000) (ψ := -195723/500000) 318 297
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t355 : ((-255500643/100000000000 : ℚ) : ℝ) ≤ stT318 355 := by
  have hc : ((-2407/50000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-255500643/100000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-2407/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c356 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-202271/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6283471/10000000) (δ := 8017/500000000) (ψ := -195723/500000) 318 297
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t356 : ((-13402084713/312500000000 : ℚ) : ℝ) ≤ stT318 356 := by
  have hc : ((-25287/31250 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13402084713/312500000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-25287/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c357 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-96541/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3597259/5000000) (δ := 8031/500000000) (ψ := -195723/500000) 318 298
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t357 : ((-51100292607/1000000000000 : ℚ) : ℝ) ≤ stT318 357 := by
  have hc : ((-96551/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).2
  have h0 : (0:ℝ) ≤ ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51100292607/1000000000000 : ℚ) : ℝ)
      = ((529257/10000000 : ℚ) : ℝ) * ((-96551/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c358 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-202739/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -621343/1250000) (δ := 8031/500000000) (ψ := -195723/500000) 318 298
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t358 : ((-107177433913/5000000000000 : ℚ) : ℝ) ≤ stT318 358 := by
  have hc : ((-202789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107177433913/5000000000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-202789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c359 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((90493/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2753171/10000000) (δ := 8031/500000000) (ψ := -195723/500000) 318 298
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t359 : ((47749749467/2000000000000 : ℚ) : ℝ) ≤ stT318 359 := by
  have hc : ((90473/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47749749467/2000000000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((90473/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c360 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((195323/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -541719/10000000) (δ := 15941/1000000000) (ψ := -195723/500000) 318 298
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t360 : ((51466832469/1000000000000 : ℚ) : ℝ) ≤ stT318 360 := by
  have hc : ((195303/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51466832469/1000000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((195303/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c361 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((393331/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1663531/10000000) (δ := 8031/500000000) (ψ := -195723/500000) 318 298
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t361 : ((41397937903/1000000000000 : ℚ) : ℝ) ≤ stT318 361 := by
  have hc : ((393281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41397937903/1000000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((393281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c362 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((25697/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 193137/500000) (δ := 15941/1000000000) (ψ := -195723/500000) 318 298
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t362 : ((3363369009/2500000000000 : ℚ) : ℝ) ≤ stT318 362 := by
  have hc : ((25597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3363369009/2500000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((25597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c363 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-188073/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6055827/10000000) (δ := 15941/1000000000) (ψ := -195723/500000) 318 298
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t363 : ((-771295849/19531250000 : ℚ) : ℝ) ≤ stT318 363 := by
  have hc : ((-94049/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-771295849/19531250000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-94049/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c364 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-493963/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7465091/10000000) (δ := 1003/62500000) (ψ := -195723/500000) 318 299
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t364 : ((-258933455859/5000000000000 : ℚ) : ℝ) ≤ stT318 364 := by
  have hc : ((-494013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258933455859/5000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-494013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c365 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-258271/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5284009/10000000) (δ := 3191/200000000) (ψ := -195723/500000) 318 299
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t365 : ((-4225356597/156250000000 : ℚ) : ℝ) ≤ stT318 365 := by
  have hc : ((-258321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4225356597/156250000000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-258321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c366 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((321431/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3108889/10000000) (δ := 3191/200000000) (ψ := -195723/500000) 318 299
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t366 : ((41990571087/2500000000000 : ℚ) : ℝ) ≤ stT318 366 := by
  have hc : ((321331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).1
  have hw2 : ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((130677/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41990571087/2500000000000 : ℚ) : ℝ)
      = ((130677/2500000 : ℚ) : ℝ) * ((321331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c367 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((46509/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -939731/10000000) (δ := 1003/62500000) (ψ := -195723/500000) 318 299
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t367 : ((606871387/12500000000 : ℚ) : ℝ) ≤ stT318 367 := by
  have hc : ((5813/6250 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).1
  have hw2 : ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((104399/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((606871387/12500000000 : ℚ) : ℝ)
      = ((104399/2000000 : ℚ) : ℝ) * ((5813/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c368 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((882607/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1223543/10000000) (δ := 3191/200000000) (ψ := -195723/500000) 318 299
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t368 : ((230019272001/5000000000000 : ℚ) : ℝ) ≤ stT318 368 := by
  have hc : ((882507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230019272001/5000000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((882507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c369 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((21669/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 676187/2000000) (δ := 1003/62500000) (ψ := -195723/500000) 318 299
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t369 : ((11275220561/1000000000000 : ℚ) : ℝ) ≤ stT318 369 := by
  have hc : ((21659/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11275220561/1000000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((21659/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c370 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-598969/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5532523/10000000) (δ := 1003/62500000) (ψ := -195723/500000) 318 299
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t370 : ((-77860398861/2500000000000 : ℚ) : ℝ) ≤ stT318 370 := by
  have hc : ((-599069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77860398861/2500000000000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-599069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c371 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-99753/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1919557/2500000) (δ := 1003/62500000) (ψ := -195723/500000) 318 299
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t371 : ((-2071778221/40000000000 : ℚ) : ℝ) ≤ stT318 371 := by
  have hc : ((-99763/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2071778221/40000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-99763/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c372 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-7069/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1177951/2000000) (δ := 1003/62500000) (ψ := -195723/500000) 318 300
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t372 : ((-91640633/2500000000 : ℚ) : ℝ) ≤ stT318 372 := by
  have hc : ((-707/1000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91640633/2500000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-707/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c373 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((68543/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1877749/5000000) (δ := 1003/62500000) (ψ := -195723/500000) 318 300
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t373 : ((1771920827/500000000000 : ℚ) : ℝ) ≤ stT318 373 := by
  have hc : ((68443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).1
  have hw2 : ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25889/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1771920827/500000000000 : ℚ) : ℝ)
      = ((25889/500000 : ℚ) : ℝ) * ((68443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c374 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((795589/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -406761/2500000) (δ := 3191/200000000) (ψ := -195723/500000) 318 300
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t374 : ((411337020543/10000000000000 : ℚ) : ℝ) ≤ stT318 374 := by
  have hc : ((795489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).1
  have hw2 : ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((517087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((411337020543/10000000000000 : ℚ) : ℝ)
      = ((517087/10000000 : ℚ) : ℝ) * ((795489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c375 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((196079/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 123961/2500000) (δ := 1003/62500000) (ψ := -195723/500000) 318 300
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t375 : ((101244279423/2000000000000 : ℚ) : ℝ) ≤ stT318 375 := by
  have hc : ((196059/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101244279423/2000000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((196059/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c376 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((250863/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2613009/10000000) (δ := 3191/200000000) (ψ := -195723/500000) 318 300
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t376 : ((12934677223/500000000000 : ℚ) : ℝ) ≤ stT318 376 := by
  have hc : ((250813/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12934677223/500000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((250813/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c377 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-9801/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4724529/10000000) (δ := 3191/200000000) (ψ := -195723/500000) 318 300
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t377 : ((-40395112691/2500000000000 : ℚ) : ℝ) ≤ stT318 377 := by
  have hc : ((-78433/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).2
  have h0 : (0:ℝ) ≤ ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40395112691/2500000000000 : ℚ) : ℝ)
      = ((515027/10000000 : ℚ) : ℝ) * ((-78433/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c378 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-11467/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1707621/2500000) (δ := 3191/200000000) (ψ := -195723/500000) 318 300
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t378 : ((-4718909637/100000000000 : ℚ) : ℝ) ≤ stT318 378 := by
  have hc : ((-45873/50000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).2
  have h0 : (0:ℝ) ≤ ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4718909637/100000000000 : ℚ) : ℝ)
      = ((102869/2000000 : ℚ) : ℝ) * ((-45873/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c379 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-908637/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -677701/1000000) (δ := 797/50000000) (ψ := -195723/500000) 318 301
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t379 : ((-233393649921/5000000000000 : ℚ) : ℝ) ≤ stT318 379 := by
  have hc : ((-908737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233393649921/5000000000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-908737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c380 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-9297/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -936437/2000000) (δ := 797/50000000) (ψ := -195723/500000) 318 301
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t380 : ((-3816696899/250000000000 : ℚ) : ℝ) ≤ stT318 380 := by
  have hc : ((-74401/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3816696899/250000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-74401/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c381 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((254343/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -518569/2000000) (δ := 16063/1000000000) (ψ := -195723/500000) 318 301
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t381 : ((26055623659/1000000000000 : ℚ) : ℝ) ≤ stT318 381 := by
  have hc : ((254293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).1
  have hw2 : ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102463/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26055623659/1000000000000 : ℚ) : ℝ)
      = ((102463/2000000 : ℚ) : ℝ) * ((254293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c382 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((122419/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -31807/625000) (δ := 797/50000000) (ψ := -195723/500000) 318 301
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t382 : ((31314275643/625000000000 : ℚ) : ℝ) ≤ stT318 382 := by
  have hc : ((244813/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31314275643/625000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((244813/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c383 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((202333/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1569457/10000000) (δ := 16063/1000000000) (ψ := -195723/500000) 318 301
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t383 : ((50475846/1220703125 : ℚ) : ℝ) ≤ stT318 383 := by
  have hc : ((50577/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50475846/1220703125 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((50577/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c384 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((113551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3642499/10000000) (δ := 16063/1000000000) (ψ := -195723/500000) 318 301
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t384 : ((5789517981/1000000000000 : ℚ) : ℝ) ≤ stT318 384 := by
  have hc : ((113451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5789517981/1000000000000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((113451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c385 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-654301/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1142027/2000000) (δ := 16063/1000000000) (ψ := -195723/500000) 318 301
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t385 : ((-20844635053/625000000000 : ℚ) : ℝ) ≤ stT318 385 := by
  have hc : ((-654401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).2
  have h0 : (0:ℝ) ≤ ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20844635053/625000000000 : ℚ) : ℝ)
      = ((31853/625000 : ℚ) : ℝ) * ((-654401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c386 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-999467/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1554473/2000000) (δ := 16063/1000000000) (ψ := -195723/500000) 318 301
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t386 : ((-508766608629/10000000000000 : ℚ) : ℝ) ≤ stT318 386 := by
  have hc : ((-999567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-508766608629/10000000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-999567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c387 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-175941/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1175739/2000000) (δ := 1597/100000000) (ψ := -195723/500000) 318 302
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t387 : ((-44724310407/1250000000000 : ℚ) : ℝ) ≤ stT318 387 := by
  have hc : ((-87983/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44724310407/1250000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-87983/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c388 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((3997/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3827039/10000000) (δ := 16033/1000000000) (ψ := -195723/500000) 318 302
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t388 : ((2024092251/1000000000000 : ℚ) : ℝ) ≤ stT318 388 := by
  have hc : ((3987/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).1
  have hw2 : ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2024092251/1000000000000 : ℚ) : ℝ)
      = ((507673/10000000 : ℚ) : ℝ) * ((3987/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c389 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((756871/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1780709/10000000) (δ := 16033/1000000000) (ψ := -195723/500000) 318 302
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t389 : ((19184901621/500000000000 : ℚ) : ℝ) ≤ stT318 389 := by
  have hc : ((756771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).1
  have hw2 : ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25351/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19184901621/500000000000 : ℚ) : ℝ)
      = ((25351/500000 : ℚ) : ℝ) * ((756771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c390 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((994581/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 130187/5000000) (δ := 16033/1000000000) (ψ := -195723/500000) 318 302
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t390 : ((503574349489/10000000000000 : ℚ) : ℝ) ≤ stT318 390 := by
  have hc : ((994481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((503574349489/10000000000000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((994481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c391 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((303513/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 229621/1000000) (δ := 16033/1000000000) (ψ := -195723/500000) 318 302
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t391 : ((153467611823/5000000000000 : ℚ) : ℝ) ≤ stT318 391 := by
  have hc : ((303463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153467611823/5000000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((303463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c392 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-79637/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4326879/10000000) (δ := 1597/100000000) (ψ := -195723/500000) 318 302
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t392 : ((-40248070899/5000000000000 : ℚ) : ℝ) ≤ stT318 392 := by
  have hc : ((-79687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).2
  have h0 : (0:ℝ) ≤ ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40248070899/5000000000000 : ℚ) : ℝ)
      = ((505077/10000000 : ℚ) : ℝ) * ((-79687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c393 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-412487/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 317619/500000) (δ := 1597/100000000) (ψ := -195723/500000) 318 302
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t393 : ((-104048844529/2500000000000 : ℚ) : ℝ) ≤ stT318 393 := by
  have hc : ((-412537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).2
  have h0 : (0:ℝ) ≤ ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104048844529/2500000000000 : ℚ) : ℝ)
      = ((252217/5000000 : ℚ) : ℝ) * ((-412537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c394 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-978551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29341/40000) (δ := 7963/500000000) (ψ := -195723/500000) 318 303
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t394 : ((-493037523243/10000000000000 : ℚ) : ℝ) ≤ stT318 394 := by
  have hc : ((-978651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).2
  have h0 : (0:ℝ) ≤ ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-493037523243/10000000000000 : ℚ) : ℝ)
      = ((503793/10000000 : ℚ) : ℝ) * ((-978651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c395 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-528843/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1330021/2500000) (δ := 7963/500000000) (ψ := -195723/500000) 318 303
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t395 : ((-53228063033/2000000000000 : ℚ) : ℝ) ≤ stT318 395 := by
  have hc : ((-528943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53228063033/2000000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-528943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c396 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((244327/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1654963/5000000) (δ := 16077/1000000000) (ψ := -195723/500000) 318 303
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t396 : ((61364231793/5000000000000 : ℚ) : ℝ) ≤ stT318 396 := by
  have hc : ((244227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).1
  have hw2 : ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251259/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61364231793/5000000000000 : ℚ) : ℝ)
      = ((251259/5000000 : ℚ) : ℝ) * ((244227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c397 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((216709/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -163117/1250000) (δ := 16077/1000000000) (ψ := -195723/500000) 318 303
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t397 : ((5437522467/125000000000 : ℚ) : ℝ) ≤ stT318 397 := by
  have hc : ((54171/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).1
  have hw2 : ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((100377/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5437522467/125000000000 : ℚ) : ℝ)
      = ((100377/2000000 : ℚ) : ℝ) * ((54171/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c398 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((961593/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5561/80000) (δ := 16077/1000000000) (ψ := -195723/500000) 318 303
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t398 : ((240976106111/5000000000000 : ℚ) : ℝ) ≤ stT318 398 := by
  have hc : ((961493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).1
  have hw2 : ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250627/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((240976106111/5000000000000 : ℚ) : ℝ)
      = ((250627/5000000 : ℚ) : ℝ) * ((961493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c399 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((237409/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1345049/5000000) (δ := 16077/1000000000) (ψ := -195723/500000) 318 303
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t399 : ((59414043367/2500000000000 : ℚ) : ℝ) ≤ stT318 399 := by
  have hc : ((237359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).1
  have hw2 : ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59414043367/2500000000000 : ℚ) : ℝ)
      = ((250313/5000000 : ℚ) : ℝ) * ((237359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c400 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-148347/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2340031/5000000) (δ := 7963/500000000) (ψ := -195723/500000) 318 303
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t400 : ((-74198648397/5000000000000 : ℚ) : ℝ) ≤ stT318 400 := by
  have hc : ((-148397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74198648397/5000000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-148397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c401 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-889039/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3332549/5000000) (δ := 16077/1000000000) (ψ := -195723/500000) 318 303
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t401 : ((-444015566403/10000000000000 : ℚ) : ℝ) ≤ stT318 401 := by
  have hc : ((-889139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-444015566403/10000000000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-889139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c402 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-118793/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7062839/10000000) (δ := 16019/1000000000) (ψ := -195723/500000) 318 304
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t402 : ((-23701934861/500000000000 : ℚ) : ℝ) ≤ stT318 402 := by
  have hc : ((-237611/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23701934861/500000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-237611/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c403 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-55971/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5087661/10000000) (δ := 999/62500000) (ψ := -195723/500000) 318 304
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t403 : ((-6971849189/312500000000 : ℚ) : ℝ) ≤ stT318 403 := by
  have hc : ((-111967/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6971849189/312500000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-111967/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c404 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((318201/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3117413/10000000) (δ := 16019/1000000000) (ψ := -195723/500000) 318 304
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t404 : ((79130486659/5000000000000 : ℚ) : ℝ) ≤ stT318 404 := by
  have hc : ((318101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).1
  have hw2 : ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((248759/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79130486659/5000000000000 : ℚ) : ℝ)
      = ((248759/5000000 : ℚ) : ℝ) * ((318101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c405 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((179139/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -576007/5000000) (δ := 16019/1000000000) (ψ := -195723/500000) 318 304
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t405 : ((89004768457/2000000000000 : ℚ) : ℝ) ≤ stT318 405 := by
  have hc : ((179119/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89004768457/2000000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((179119/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c406 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((237039/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 101067/1250000) (δ := 999/62500000) (ψ := -195723/500000) 318 304
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t406 : ((58813957537/1250000000000 : ℚ) : ℝ) ≤ stT318 406 := by
  have hc : ((118507/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58813957537/1250000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((118507/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c407 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((224257/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 691059/2500000) (δ := 999/62500000) (ψ := -195723/500000) 318 304
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t407 : ((111135149967/5000000000000 : ℚ) : ℝ) ≤ stT318 407 := by
  have hc : ((224207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111135149967/5000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((224207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c408 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-310073/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2357583/5000000) (δ := 999/62500000) (ψ := -195723/500000) 318 304
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t408 : ((-76779293901/5000000000000 : ℚ) : ℝ) ≤ stT318 408 := by
  have hc : ((-310173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).2
  have h0 : (0:ℝ) ≤ ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76779293901/5000000000000 : ℚ) : ℝ)
      = ((247537/5000000 : ℚ) : ℝ) * ((-310173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c409 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-222087/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3330663/5000000) (δ := 999/62500000) (ψ := -195723/500000) 318 304
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t409 : ((-3432109329/78125000000 : ℚ) : ℝ) ≤ stT318 409 := by
  have hc : ((-13882/15625 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).2
  have h0 : (0:ℝ) ≤ ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3432109329/78125000000 : ℚ) : ℝ)
      = ((494469/10000000 : ℚ) : ℝ) * ((-13882/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c410 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-477743/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7105247/10000000) (δ := 16091/1000000000) (ψ := -195723/500000) 318 305
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t410 : ((-47193047989/1000000000000 : ℚ) : ℝ) ≤ stT318 410 := by
  have hc : ((-477793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).2
  have h0 : (0:ℝ) ≤ ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47193047989/1000000000000 : ℚ) : ℝ)
      = ((98773/2000000 : ℚ) : ℝ) * ((-477793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c411 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-476459/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1292137/2500000) (δ := 1989/125000000) (ψ := -195723/500000) 318 305
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t411 : ((-14691837411/625000000000 : ℚ) : ℝ) ≤ stT318 411 := by
  have hc : ((-476559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14691837411/625000000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-476559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c412 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((272653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1618309/5000000) (δ := 16091/1000000000) (ψ := -195723/500000) 318 305
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t412 : ((16784631399/1250000000000 : ℚ) : ℝ) ≤ stT318 412 := by
  have hc : ((272553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16784631399/1250000000000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((272553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c413 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((865949/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1309379/10000000) (δ := 16091/1000000000) (ψ := -195723/500000) 318 305
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t413 : ((426055719883/10000000000000 : ℚ) : ℝ) ≤ stT318 413 := by
  have hc : ((865849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).1
  have hw2 : ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((492067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((426055719883/10000000000000 : ℚ) : ℝ)
      = ((492067/10000000 : ℚ) : ℝ) * ((865849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c414 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((194013/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 613249/10000000) (δ := 16091/1000000000) (ψ := -195723/500000) 318 305
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t414 : ((95342321689/2000000000000 : ℚ) : ℝ) ≤ stT318 414 := by
  have hc : ((193993/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).1
  have hw2 : ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((491473/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95342321689/2000000000000 : ℚ) : ℝ)
      = ((491473/10000000 : ℚ) : ℝ) * ((193993/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c415 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((529737/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1265633/5000000) (δ := 16091/1000000000) (ψ := -195723/500000) 318 305
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t415 : ((406231579/15625000000 : ℚ) : ℝ) ≤ stT318 415 := by
  have hc : ((529637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).1
  have hw2 : ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((767/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((406231579/15625000000 : ℚ) : ℝ)
      = ((767/15625 : ℚ) : ℝ) * ((529637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c416 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-51391/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 277787/625000) (δ := 1989/125000000) (ψ := -195723/500000) 318 305
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t416 : ((-3151100257/312500000000 : ℚ) : ℝ) ≤ stT318 416 := by
  have hc : ((-6427/31250 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3151100257/312500000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-6427/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c417 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-825201/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6353387/10000000) (δ := 1989/125000000) (ψ := -195723/500000) 318 305
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t417 : ((-404152375603/10000000000000 : ℚ) : ℝ) ≤ stT318 417 := by
  have hc : ((-825301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-404152375603/10000000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-825301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c418 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-493499/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -931299/1250000) (δ := 7999/500000000) (ψ := -195723/500000) 318 306
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t418 : ((-60350678171/1250000000000 : ℚ) : ℝ) ≤ stT318 418 := by
  have hc : ((-493549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).2
  have h0 : (0:ℝ) ≤ ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60350678171/1250000000000 : ℚ) : ℝ)
      = ((122279/2500000 : ℚ) : ℝ) * ((-493549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c419 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-151197/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -277537/500000) (δ := 3201/200000000) (ψ := -195723/500000) 318 306
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t419 : ((-9234598263/312500000000 : ℚ) : ℝ) ≤ stT318 419 := by
  have hc : ((-75611/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).2
  have h0 : (0:ℝ) ≤ ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9234598263/312500000000 : ℚ) : ℝ)
      = ((122133/2500000 : ℚ) : ℝ) * ((-75611/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c420 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((6771/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3655619/10000000) (δ := 3201/200000000) (ψ := -195723/500000) 318 306
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t420 : ((264068781/50000000000 : ℚ) : ℝ) ≤ stT318 420 := by
  have hc : ((27059/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((264068781/50000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((27059/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c421 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((190239/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1765029/10000000) (δ := 7999/500000000) (ψ := -195723/500000) 318 306
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t421 : ((4635229859/125000000000 : ℚ) : ℝ) ≤ stT318 421 := by
  have hc : ((95107/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4635229859/125000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((95107/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c422 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((998827/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30277/2500000) (δ := 3201/200000000) (ψ := -195723/500000) 318 306
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t422 : ((60771539223/1250000000000 : ℚ) : ℝ) ≤ stT318 422 := by
  have hc : ((998727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60771539223/1250000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((998727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c423 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((86991/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1001357/5000000) (δ := 3201/200000000) (ψ := -195723/500000) 318 306
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t423 : ((10572584589/312500000000 : ℚ) : ℝ) ≤ stT318 423 := by
  have hc : ((173957/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10572584589/312500000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((173957/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c424 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((294/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 969987/2500000) (δ := 7999/500000000) (ψ := -195723/500000) 318 306
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t424 : ((1136159459/1250000000000 : ℚ) : ℝ) ≤ stT318 424 := by
  have hc : ((4679/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1136159459/1250000000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((4679/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c425 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-66709/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5752729/10000000) (δ := 3201/200000000) (ψ := -195723/500000) 318 306
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t425 : ((-2022719923/62500000000 : ℚ) : ℝ) ≤ stT318 425 := by
  have hc : ((-66719/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2022719923/62500000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-66719/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c426 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-497833/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3810569/5000000) (δ := 3201/200000000) (ψ := -195723/500000) 318 306
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t426 : ((-120612654633/2500000000000 : ℚ) : ℝ) ≤ stT318 426 := by
  have hc : ((-497883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120612654633/2500000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-497883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c427 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-397291/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6222789/10000000) (δ := 16097/1000000000) (ψ := -195723/500000) 318 307
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t427 : ((-96143409747/2500000000000 : ℚ) : ℝ) ≤ stT318 427 := by
  have hc : ((-397341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96143409747/2500000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-397341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c428 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-173601/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1090801/2500000) (δ := 7953/500000000) (ψ := -195723/500000) 318 307
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t428 : ((-83961678669/10000000000000 : ℚ) : ℝ) ≤ stT318 428 := by
  have hc : ((-173701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83961678669/10000000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-173701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c429 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((537663/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2507833/10000000) (δ := 7953/500000000) (ψ := -195723/500000) 318 307
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t429 : ((64884391663/2500000000000 : ℚ) : ℝ) ≤ stT318 429 := by
  have hc : ((537563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).1
  have hw2 : ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((120701/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64884391663/2500000000000 : ℚ) : ℝ)
      = ((120701/2500000 : ℚ) : ℝ) * ((537563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c430 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((241421/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -131367/2000000) (δ := 16097/1000000000) (ψ := -195723/500000) 318 307
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t430 : ((14551411229/312500000000 : ℚ) : ℝ) ≤ stT318 430 := by
  have hc : ((60349/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).1
  have hw2 : ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((241121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14551411229/312500000000 : ℚ) : ℝ)
      = ((241121/5000000 : ℚ) : ℝ) * ((60349/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c431 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((888873/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1189791/10000000) (δ := 16097/1000000000) (ψ := -195723/500000) 318 307
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t431 : ((428106844959/10000000000000 : ℚ) : ℝ) ≤ stT318 431 := by
  have hc : ((888773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((428106844959/10000000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((888773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c432 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((175161/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 758051/2500000) (δ := 7953/500000000) (ψ := -195723/500000) 318 307
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t432 : ((674002239/40000000000 : ℚ) : ℝ) ≤ stT318 432 := by
  have hc : ((175111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((674002239/40000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((175111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c433 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-46059/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4870403/10000000) (δ := 7953/500000000) (ψ := -195723/500000) 318 307
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t433 : ((-4428116151/250000000000 : ℚ) : ℝ) ≤ stT318 433 := by
  have hc : ((-92143/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).2
  have h0 : (0:ℝ) ≤ ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4428116151/250000000000 : ℚ) : ℝ)
      = ((48057/1000000 : ℚ) : ℝ) * ((-92143/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c434 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-896111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6704309/10000000) (δ := 7953/500000000) (ψ := -195723/500000) 318 307
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t434 : ((-26887226211/625000000000 : ℚ) : ℝ) ≤ stT318 434 := by
  have hc : ((-896211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).2
  have h0 : (0:ℝ) ≤ ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26887226211/625000000000 : ℚ) : ℝ)
      = ((30001/625000 : ℚ) : ℝ) * ((-896211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c435 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-963233/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3586981/5000000) (δ := 1599/100000000) (ψ := -195723/500000) 318 308
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t435 : ((-57735436689/1250000000000 : ℚ) : ℝ) ≤ stT318 435 := by
  have hc : ((-963333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).2
  have h0 : (0:ℝ) ≤ ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57735436689/1250000000000 : ℚ) : ℝ)
      = ((59933/1250000 : ℚ) : ℝ) * ((-963333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c436 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-10769/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5348483/10000000) (δ := 1599/100000000) (ψ := -195723/500000) 318 308
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t436 : ((-2579191347/100000000000 : ℚ) : ℝ) ≤ stT318 436 := by
  have hc : ((-10771/20000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).2
  have h0 : (0:ℝ) ≤ ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2579191347/100000000000 : ℚ) : ℝ)
      = ((239457/5000000 : ℚ) : ℝ) * ((-10771/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c437 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((159229/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3527217/10000000) (δ := 16013/1000000000) (ψ := -195723/500000) 318 308
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t437 : ((19030396239/2500000000000 : ℚ) : ℝ) ≤ stT318 437 := by
  have hc : ((159129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).1
  have hw2 : ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((119591/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19030396239/2500000000000 : ℚ) : ℝ)
      = ((119591/2500000 : ℚ) : ℝ) * ((159129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c438 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((15501/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -855003/5000000) (δ := 16013/1000000000) (ψ := -195723/500000) 318 308
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t438 : ((3702850591/100000000000 : ℚ) : ℝ) ≤ stT318 438 := by
  have hc : ((15499/20000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).1
  have hw2 : ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((238909/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3702850591/100000000000 : ℚ) : ℝ)
      = ((238909/5000000 : ℚ) : ℝ) * ((15499/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c439 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((62447/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102991/10000000) (δ := 1599/100000000) (ψ := -195723/500000) 318 308
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t439 : ((119205136299/2500000000000 : ℚ) : ℝ) ≤ stT318 439 := by
  have hc : ((249763/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).1
  have hw2 : ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((477273/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119205136299/2500000000000 : ℚ) : ℝ)
      = ((477273/10000000 : ℚ) : ℝ) * ((249763/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c440 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((721561/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 382371/2000000) (δ := 16013/1000000000) (ψ := -195723/500000) 318 308
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t440 : ((343942823991/10000000000000 : ℚ) : ℝ) ≤ stT318 440 := by
  have hc : ((721461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).1
  have hw2 : ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((343942823991/10000000000000 : ℚ) : ℝ)
      = ((476731/10000000 : ℚ) : ℝ) * ((721461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c441 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((84063/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 464573/1250000) (δ := 1599/100000000) (ψ := -195723/500000) 318 308
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t441 : ((3998234097/1000000000000 : ℚ) : ℝ) ≤ stT318 441 := by
  have hc : ((83963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).1
  have hw2 : ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((47619/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3998234097/1000000000000 : ℚ) : ℝ)
      = ((47619/1000000 : ℚ) : ℝ) * ((83963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c442 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-594069/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5517259/10000000) (δ := 1599/100000000) (ψ := -195723/500000) 318 308
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t442 : ((-70654418297/2500000000000 : ℚ) : ℝ) ≤ stT318 442 := by
  have hc : ((-594169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70654418297/2500000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-594169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c443 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-488377/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 182847/250000) (δ := 16013/1000000000) (ψ := -195723/500000) 318 308
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t443 : ((-46411798821/1000000000000 : ℚ) : ℝ) ≤ stT318 443 := by
  have hc : ((-488427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46411798821/1000000000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-488427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c444 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-87711/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3300759/5000000) (δ := 16083/1000000000) (ψ := -195723/500000) 318 309
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t444 : ((-41630544459/1000000000000 : ℚ) : ℝ) ≤ stT318 444 := by
  have hc : ((-87721/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41630544459/1000000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-87721/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c445 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-347033/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2406503/5000000) (δ := 199/12500000) (ψ := -195723/500000) 318 309
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t445 : ((-82278505059/5000000000000 : ℚ) : ℝ) ≤ stT318 445 := by
  have hc : ((-347133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).2
  have h0 : (0:ℝ) ≤ ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82278505059/5000000000000 : ℚ) : ℝ)
      = ((237023/5000000 : ℚ) : ℝ) * ((-347133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c446 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((8793/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -302847/1000000) (δ := 16083/1000000000) (ψ := -195723/500000) 318 309
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t446 : ((8324832053/500000000000 : ℚ) : ℝ) ≤ stT318 446 := by
  have hc : ((17581/50000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8324832053/500000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((17581/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c447 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((54873/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -311997/2500000) (δ := 16083/1000000000) (ψ := -195723/500000) 318 309
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t447 : ((103804160061/2500000000000 : ℚ) : ℝ) ≤ stT318 447 := by
  have hc : ((219467/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103804160061/2500000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((219467/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c448 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((97773/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 528599/10000000) (δ := 199/12500000) (ψ := -195723/500000) 318 309
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t448 : ((9237723633/200000000000 : ℚ) : ℝ) ≤ stT318 448 := by
  have hc : ((97763/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9237723633/200000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((97763/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c449 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((30273/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2301131/10000000) (δ := 199/12500000) (ψ := -195723/500000) 318 309
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t449 : ((3571086743/125000000000 : ℚ) : ℝ) ≤ stT318 449 := by
  have hc : ((7567/12500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3571086743/125000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((7567/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c450 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-57079/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4069767/10000000) (δ := 16083/1000000000) (ψ := -195723/500000) 318 309
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t450 : ((-5390893299/2000000000000 : ℚ) : ℝ) ≤ stT318 450 := by
  have hc : ((-57179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).2
  have h0 : (0:ℝ) ≤ ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5390893299/2000000000000 : ℚ) : ℝ)
      = ((94281/2000000 : ℚ) : ℝ) * ((-57179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c451 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-345549/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1458627/2500000) (δ := 16083/1000000000) (ψ := -195723/500000) 318 309
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t451 : ((-81368174159/2500000000000 : ℚ) : ℝ) ≤ stT318 451 := by
  have hc : ((-345599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81368174159/2500000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-345599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c452 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-19893/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3797637/5000000) (δ := 16083/1000000000) (ψ := -195723/500000) 318 309
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t452 : ((-1871566419/40000000000 : ℚ) : ℝ) ≤ stT318 452 := by
  have hc : ((-3979/4000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1871566419/40000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-3979/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c453 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-206433/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6355739/10000000) (δ := 1997/125000000) (ψ := -195723/500000) 318 310
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t453 : ((-48501216589/1250000000000 : ℚ) : ℝ) ≤ stT318 453 := by
  have hc : ((-103229/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48501216589/1250000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-103229/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c454 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-267029/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1150691/2500000) (δ := 1997/125000000) (ψ := -195723/500000) 318 310
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t454 : ((-31342512699/2500000000000 : ℚ) : ℝ) ≤ stT318 454 := by
  have hc : ((-267129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31342512699/2500000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-267129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c455 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((416313/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -114141/400000) (δ := 16027/1000000000) (ψ := -195723/500000) 318 310
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t455 : ((195123567891/10000000000000 : ℚ) : ℝ) ≤ stT318 455 := by
  have hc : ((416213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).1
  have hw2 : ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((468807/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((195123567891/10000000000000 : ℚ) : ℝ)
      = ((468807/10000000 : ℚ) : ℝ) * ((416213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c456 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((903353/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -554091/5000000) (δ := 16027/1000000000) (ψ := -195723/500000) 318 310
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t456 : ((105746538469/2500000000000 : ℚ) : ℝ) ≤ stT318 456 := by
  have hc : ((903253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).1
  have hw2 : ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117073/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105746538469/2500000000000 : ℚ) : ℝ)
      = ((117073/2500000 : ℚ) : ℝ) * ((903253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c457 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((968089/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126653/2000000) (δ := 1997/125000000) (ψ := -195723/500000) 318 310
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t457 : ((22640294721/500000000000 : ℚ) : ℝ) ≤ stT318 457 := by
  have hc : ((967989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22640294721/500000000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((967989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c458 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((36437/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 74093/312500) (δ := 1997/125000000) (ψ := -195723/500000) 318 310
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t458 : ((68091840487/2500000000000 : ℚ) : ℝ) ≤ stT318 458 := by
  have hc : ((145723/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68091840487/2500000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((145723/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c459 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-17781/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4104951/10000000) (δ := 16027/1000000000) (ψ := -195723/500000) 318 310
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t459 : ((-4155573183/1250000000000 : ℚ) : ℝ) ≤ stT318 459 := by
  have hc : ((-8903/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).2
  have h0 : (0:ℝ) ≤ ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4155573183/1250000000000 : ℚ) : ℝ)
      = ((466761/10000000 : ℚ) : ℝ) * ((-8903/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c460 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-691249/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 583503/1000000) (δ := 16027/1000000000) (ψ := -195723/500000) 318 310
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t460 : ((-322343545297/10000000000000 : ℚ) : ℝ) ≤ stT318 460 := by
  have hc : ((-691349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).2
  have h0 : (0:ℝ) ≤ ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-322343545297/10000000000000 : ℚ) : ℝ)
      = ((466253/10000000 : ℚ) : ℝ) * ((-691349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c461 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-496581/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1890363/2500000) (δ := 16027/1000000000) (ψ := -195723/500000) 318 310
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t461 : ((-231304398357/5000000000000 : ℚ) : ℝ) ≤ stT318 461 := by
  have hc : ((-496631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).2
  have h0 : (0:ℝ) ≤ ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-231304398357/5000000000000 : ℚ) : ℝ)
      = ((465747/10000000 : ℚ) : ℝ) * ((-496631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c462 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-210201/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3211953/5000000) (δ := 16069/1000000000) (ψ := -195723/500000) 318 311
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t462 : ((-48903087459/1250000000000 : ℚ) : ℝ) ≤ stT318 462 := by
  have hc : ((-105113/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).2
  have h0 : (0:ℝ) ≤ ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48903087459/1250000000000 : ℚ) : ℝ)
      = ((465243/10000000 : ℚ) : ℝ) * ((-105113/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c463 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-76547/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4704957/10000000) (δ := 16069/1000000000) (ψ := -195723/500000) 318 311
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t463 : ((-444825891/31250000000 : ℚ) : ℝ) ≤ stT318 463 := by
  have hc : ((-19143/62500 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).2
  have h0 : (0:ℝ) ≤ ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-444825891/31250000000 : ℚ) : ℝ)
      = ((23237/500000 : ℚ) : ℝ) * ((-19143/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c464 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((183089/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186859/625000) (δ := 7967/500000000) (ψ := -195723/500000) 318 311
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t464 : ((42486829641/2500000000000 : ℚ) : ℝ) ≤ stT318 464 := by
  have hc : ((183039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42486829641/2500000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((183039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c465 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((872121/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1278189/10000000) (δ := 16069/1000000000) (ψ := -195723/500000) 318 311
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t465 : ((202194637249/5000000000000 : ℚ) : ℝ) ≤ stT318 465 := by
  have hc : ((872021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202194637249/5000000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((872021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c466 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((98527/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42963/1000000) (δ := 16069/1000000000) (ψ := -195723/500000) 318 311
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t466 : ((45637113597/1000000000000 : ℚ) : ℝ) ≤ stT318 466 := by
  have hc : ((98517/100000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45637113597/1000000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((98517/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c467 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((657337/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66681/312500) (δ := 16069/1000000000) (ψ := -195723/500000) 318 311
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t467 : ((38016559791/1250000000000 : ℚ) : ℝ) ≤ stT318 467 := by
  have hc : ((657237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).1
  have hw2 : ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57843/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38016559791/1250000000000 : ℚ) : ℝ)
      = ((57843/1250000 : ℚ) : ℝ) * ((657237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c468 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((37069/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3834297/10000000) (δ := 16069/1000000000) (ψ := -195723/500000) 318 311
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t468 : ((68355681/40000000000 : ℚ) : ℝ) ≤ stT318 468 := by
  have hc : ((36969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).1
  have hw2 : ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68355681/40000000000 : ℚ) : ℝ)
      = ((1849/40000 : ℚ) : ℝ) * ((36969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c469 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-598553/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 221249/400000) (δ := 7967/500000000) (ψ := -195723/500000) 318 311
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t469 : ((-138216405987/5000000000000 : ℚ) : ℝ) ≤ stT318 469 := by
  have hc : ((-598653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138216405987/5000000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-598653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c470 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-968467/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1444899/2000000) (δ := 16069/1000000000) (ψ := -195723/500000) 318 311
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t470 : ((-223383512911/5000000000000 : ℚ) : ℝ) ≤ stT318 470 := by
  have hc : ((-968567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223383512911/5000000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-968567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c471 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-911417/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -271751/400000) (δ := 15961/1000000000) (ψ := -195723/500000) 318 312
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t471 : ((-52500644649/1250000000000 : ℚ) : ℝ) ≤ stT318 471 := by
  have hc : ((-911517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52500644649/1250000000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-911517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c472 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-454907/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5107659/10000000) (δ := 8021/500000000) (ψ := -195723/500000) 318 312
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t472 : ((-409051293/19531250000 : ℚ) : ℝ) ≤ stT318 472 := by
  have hc : ((-455007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).2
  have h0 : (0:ℝ) ≤ ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-409051293/19531250000 : ℚ) : ℝ)
      = ((3596/78125 : ℚ) : ℝ) * ((-455007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c473 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((99701/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3425121/10000000) (δ := 8021/500000000) (ψ := -195723/500000) 318 312
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t473 : ((229097649/25000000000 : ℚ) : ℝ) ≤ stT318 473 := by
  have hc : ((99651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229097649/25000000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((99651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c474 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((765851/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1746081/10000000) (δ := 8021/500000000) (ψ := -195723/500000) 318 312
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t474 : ((70344184113/2000000000000 : ℚ) : ℝ) ≤ stT318 474 := by
  have hc : ((765751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70344184113/2000000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((765751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c475 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((999601/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -70619/10000000) (δ := 15961/1000000000) (ψ := -195723/500000) 318 312
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t475 : ((458602043331/10000000000000 : ℚ) : ℝ) ≤ stT318 475 := by
  have hc : ((999501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((458602043331/10000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((999501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c476 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((801793/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 800633/5000000) (δ := 15961/1000000000) (ψ := -195723/500000) 318 312
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t476 : ((367455184857/10000000000000 : ℚ) : ℝ) ≤ stT318 476 := by
  have hc : ((801693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((367455184857/10000000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((801693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c477 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((64979/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3269653/10000000) (δ := 15961/1000000000) (ψ := -195723/500000) 318 312
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t477 : ((3717544759/312500000000 : ℚ) : ℝ) ≤ stT318 477 := by
  have hc : ((32477/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3717544759/312500000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((32477/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c478 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-98057/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2467311/5000000) (δ := 8021/500000000) (ψ := -195723/500000) 318 312
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t478 : ((-2243086299/125000000000 : ℚ) : ℝ) ≤ stT318 478 := by
  have hc : ((-49041/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2243086299/125000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-49041/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c479 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-17521/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6596013/10000000) (δ := 8021/500000000) (ψ := -195723/500000) 318 312
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t479 : ((-500404311/12500000000 : ℚ) : ℝ) ≤ stT318 479 := by
  have hc : ((-17523/20000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-500404311/12500000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-17523/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c480 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-493611/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7453899/10000000) (δ := 8027/500000000) (ψ := -195723/500000) 318 313
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t480 : ((-56331163049/1250000000000 : ℚ) : ℝ) ≤ stT318 480 := by
  have hc : ((-493661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56331163049/1250000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-493661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c481 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-680887/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -45308/78125) (δ := 15949/1000000000) (ψ := -195723/500000) 318 313
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t481 : ((-310503513507/10000000000000 : ℚ) : ℝ) ≤ stT318 481 := by
  have hc : ((-680987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310503513507/10000000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-680987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c482 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-22101/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4148289/10000000) (δ := 8027/500000000) (ψ := -195723/500000) 318 313
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t482 : ((-78735371/19531250000 : ℚ) : ℝ) ≤ stT318 482 := by
  have hc : ((-11063/125000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).2
  have h0 : (0:ℝ) ≤ ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78735371/19531250000 : ℚ) : ℝ)
      = ((7117/156250 : ℚ) : ℝ) * ((-11063/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c483 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((540083/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2500651/10000000) (δ := 15949/1000000000) (ψ := -195723/500000) 318 313
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t483 : ((49140072949/2000000000000 : ℚ) : ℝ) ≤ stT318 483 := by
  have hc : ((539983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49140072949/2000000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((539983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c484 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((58869/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -856353/10000000) (δ := 8027/500000000) (ψ := -195723/500000) 318 313
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t484 : ((21404614959/500000000000 : ℚ) : ℝ) ≤ stT318 484 := by
  have hc : ((235451/250000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21404614959/500000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((235451/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c485 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((475587/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12257/156250) (δ := 15949/1000000000) (ψ := -195723/500000) 318 313
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t485 : ((53982484703/1250000000000 : ℚ) : ℝ) ≤ stT318 485 := by
  have hc : ((475537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53982484703/1250000000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((475537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c486 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((566293/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2421989/10000000) (δ := 15949/1000000000) (ψ := -195723/500000) 318 313
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t486 : ((256830240537/10000000000000 : ℚ) : ℝ) ≤ stT318 486 := by
  have hc : ((566193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((256830240537/10000000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((566193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c487 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-413/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4056111/10000000) (δ := 8027/500000000) (ψ := -195723/500000) 318 313
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t487 : ((-117194367/50000000000 : ℚ) : ℝ) ≤ stT318 487 := by
  have hc : ((-2069/40000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).2
  have h0 : (0:ℝ) ≤ ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117194367/50000000000 : ℚ) : ℝ)
      = ((56643/1250000 : ℚ) : ℝ) * ((-2069/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c488 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-647243/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1137379/2000000) (δ := 15949/1000000000) (ψ := -195723/500000) 318 313
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t488 : ((-293038581897/10000000000000 : ℚ) : ℝ) ≤ stT318 488 := by
  have hc : ((-647343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-293038581897/10000000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-647343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c489 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-488393/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 365713/500000) (δ := 15949/1000000000) (ψ := -195723/500000) 318 313
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t489 : ((-27610217461/625000000000 : ℚ) : ℝ) ≤ stT318 489 := by
  have hc : ((-488443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27610217461/625000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-488443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c490 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-181479/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3384799/5000000) (δ := 15947/1000000000) (ψ := -195723/500000) 318 314
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t490 : ((-40996449623/1000000000000 : ℚ) : ℝ) ≤ stT318 490 := by
  have hc : ((-181499/200000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40996449623/1000000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-181499/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c491 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-234741/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -321797/625000) (δ := 15947/1000000000) (ψ := -195723/500000) 318 314
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t491 : ((-52979884777/2500000000000 : ℚ) : ℝ) ≤ stT318 491 := by
  have hc : ((-234791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52979884777/2500000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-234791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c492 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((78819/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -706249/2000000) (δ := 15947/1000000000) (ψ := -195723/500000) 318 314
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t492 : ((17755871673/2500000000000 : ℚ) : ℝ) ≤ stT318 492 := by
  have hc : ((78769/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17755871673/2500000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((78769/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c493 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((720113/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1917077/10000000) (δ := 15947/1000000000) (ψ := -195723/500000) 318 314
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t493 : ((324277294901/10000000000000 : ℚ) : ℝ) ≤ stT318 493 := by
  have hc : ((720013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((324277294901/10000000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((720013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c494 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((496257/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -306089/10000000) (δ := 15947/1000000000) (ψ := -195723/500000) 318 314
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t494 : ((223253949647/5000000000000 : ℚ) : ℝ) ≤ stT318 494 := by
  have hc : ((496207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((223253949647/5000000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((496207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c495 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((867509/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 32539/250000) (δ := 15947/1000000000) (ψ := -195723/500000) 318 314
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t495 : ((194935426797/5000000000000 : ℚ) : ℝ) ≤ stT318 495 := by
  have hc : ((867409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194935426797/5000000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((867409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c496 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((397127/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2906029/10000000) (δ := 15947/1000000000) (ψ := -195723/500000) 318 314
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t496 : ((178270284351/10000000000000 : ℚ) : ℝ) ≤ stT318 496 := by
  have hc : ((397027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178270284351/10000000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((397027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c497 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-230021/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4507239/10000000) (δ := 2007/125000000) (ψ := -195723/500000) 318 314
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t497 : ((-51611768001/5000000000000 : ℚ) : ℝ) ≤ stT318 497 := by
  have hc : ((-230121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51611768001/5000000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-230121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c498 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-765153/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6105189/10000000) (δ := 2007/125000000) (ψ := -195723/500000) 318 314
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t498 : ((-342918287083/10000000000000 : ℚ) : ℝ) ≤ stT318 498 := by
  have hc : ((-765253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-342918287083/10000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-765253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c499 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-998103/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7699959/10000000) (δ := 2007/125000000) (ψ := -195723/500000) 318 314
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t499 : ((-223428775693/5000000000000 : ℚ) : ℝ) ≤ stT318 499 := by
  have hc : ((-998203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223428775693/5000000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-998203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_c500 :
    |Real.cos (((318 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-419589/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1283283/2000000) (δ := 401/25000000) (ψ := -195723/500000) 318 315
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st318_t500 : ((-93834217873/2500000000000 : ℚ) : ℝ) ≤ stT318 500 := by
  have hc : ((-419639/500000 : ℚ) : ℝ)
      ≤ Real.cos (((318 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st318_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).2
  have h0 : (0:ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93834217873/2500000000000 : ℚ) : ℝ)
      = ((223607/5000000 : ℚ) : ℝ) * ((-419639/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st318_p1 : ((462129/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT318 (i+1) := by
  rw [Finset.sum_range_one]
  exact st318_t1

theorem st318_p2 : ((13633139850573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT318 (i+1))
      = (∑ i ∈ Finset.range 1, stT318 (i+1)) + stT318 2 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 1
    simpa using h
  have hprev := st318_p1
  have hstep := st318_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p3 : ((10676886921459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT318 (i+1))
      = (∑ i ∈ Finset.range 2, stT318 (i+1)) + stT318 3 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 2
    simpa using h
  have hprev := st318_p2
  have hstep := st318_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p4 : ((11476526921459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT318 (i+1))
      = (∑ i ∈ Finset.range 3, stT318 (i+1)) + stT318 4 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 3
    simpa using h
  have hprev := st318_p3
  have hstep := st318_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p5 : ((7032520656899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT318 (i+1))
      = (∑ i ∈ Finset.range 4, stT318 (i+1)) + stT318 5 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 4
    simpa using h
  have hprev := st318_p4
  have hstep := st318_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p6 : ((6917345646503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT318 (i+1))
      = (∑ i ∈ Finset.range 5, stT318 (i+1)) + stT318 6 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 5
    simpa using h
  have hprev := st318_p5
  have hstep := st318_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p7 : ((412866923371/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT318 (i+1))
      = (∑ i ∈ Finset.range 6, stT318 (i+1)) + stT318 7 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 6
    simpa using h
  have hprev := st318_p6
  have hstep := st318_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p8 : ((209488938111/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT318 (i+1))
      = (∑ i ∈ Finset.range 7, stT318 (i+1)) + stT318 8 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 7
    simpa using h
  have hprev := st318_p7
  have hstep := st318_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p9 : ((873447989089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT318 (i+1))
      = (∑ i ∈ Finset.range 8, stT318 (i+1)) + stT318 9 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 8
    simpa using h
  have hprev := st318_p8
  have hstep := st318_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p10 : ((-411353939531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT318 (i+1))
      = (∑ i ∈ Finset.range 9, stT318 (i+1)) + stT318 10 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 9
    simpa using h
  have hprev := st318_p9
  have hstep := st318_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p11 : ((-872643553699/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT318 (i+1))
      = (∑ i ∈ Finset.range 10, stT318 (i+1)) + stT318 11 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 10
    simpa using h
  have hprev := st318_p10
  have hstep := st318_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p12 : ((-430945460559/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT318 (i+1))
      = (∑ i ∈ Finset.range 11, stT318 (i+1)) + stT318 12 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 11
    simpa using h
  have hprev := st318_p11
  have hstep := st318_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p13 : ((-32293664559/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT318 (i+1))
      = (∑ i ∈ Finset.range 12, stT318 (i+1)) + stT318 13 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 12
    simpa using h
  have hprev := st318_p12
  have hstep := st318_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p14 : ((-251421023799/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT318 (i+1))
      = (∑ i ∈ Finset.range 13, stT318 (i+1)) + stT318 14 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 13
    simpa using h
  have hprev := st318_p13
  have hstep := st318_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p15 : ((-32826634533/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT318 (i+1))
      = (∑ i ∈ Finset.range 14, stT318 (i+1)) + stT318 15 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 14
    simpa using h
  have hprev := st318_p14
  have hstep := st318_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p16 : ((-1011391147361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT318 (i+1))
      = (∑ i ∈ Finset.range 15, stT318 (i+1)) + stT318 16 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 15
    simpa using h
  have hprev := st318_p15
  have hstep := st318_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p17 : ((-1087840674927/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT318 (i+1))
      = (∑ i ∈ Finset.range 16, stT318 (i+1)) + stT318 17 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 16
    simpa using h
  have hprev := st318_p16
  have hstep := st318_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p18 : ((-5709213008709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT318 (i+1))
      = (∑ i ∈ Finset.range 17, stT318 (i+1)) + stT318 18 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 17
    simpa using h
  have hprev := st318_p17
  have hstep := st318_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p19 : ((-3728199262581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT318 (i+1))
      = (∑ i ∈ Finset.range 18, stT318 (i+1)) + stT318 19 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 18
    simpa using h
  have hprev := st318_p18
  have hstep := st318_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p20 : ((-4678968667977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT318 (i+1))
      = (∑ i ∈ Finset.range 19, stT318 (i+1)) + stT318 20 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 19
    simpa using h
  have hprev := st318_p19
  have hstep := st318_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p21 : ((-3390486392631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT318 (i+1))
      = (∑ i ∈ Finset.range 20, stT318 (i+1)) + stT318 21 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 20
    simpa using h
  have hprev := st318_p20
  have hstep := st318_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p22 : ((-5522070123039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT318 (i+1))
      = (∑ i ∈ Finset.range 21, stT318 (i+1)) + stT318 22 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 21
    simpa using h
  have hprev := st318_p21
  have hstep := st318_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p23 : ((-5474428752927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT318 (i+1))
      = (∑ i ∈ Finset.range 22, stT318 (i+1)) + stT318 23 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 22
    simpa using h
  have hprev := st318_p22
  have hstep := st318_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p24 : ((-3767506286389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT318 (i+1))
      = (∑ i ∈ Finset.range 23, stT318 (i+1)) + stT318 24 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 23
    simpa using h
  have hprev := st318_p23
  have hstep := st318_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p25 : ((-1794948286389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT318 (i+1))
      = (∑ i ∈ Finset.range 24, stT318 (i+1)) + stT318 25 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 24
    simpa using h
  have hprev := st318_p24
  have hstep := st318_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p26 : ((12548783371/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT318 (i+1))
      = (∑ i ∈ Finset.range 25, stT318 (i+1)) + stT318 26 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 25
    simpa using h
  have hprev := st318_p25
  have hstep := st318_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p27 : ((351738621617/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT318 (i+1))
      = (∑ i ∈ Finset.range 26, stT318 (i+1)) + stT318 27 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 26
    simpa using h
  have hprev := st318_p26
  have hstep := st318_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p28 : ((116252009539/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT318 (i+1))
      = (∑ i ∈ Finset.range 27, stT318 (i+1)) + stT318 28 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 27
    simpa using h
  have hprev := st318_p27
  have hstep := st318_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p29 : ((-459672419391/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT318 (i+1))
      = (∑ i ∈ Finset.range 28, stT318 (i+1)) + stT318 29 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 28
    simpa using h
  have hprev := st318_p28
  have hstep := st318_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p30 : ((-368717784851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT318 (i+1))
      = (∑ i ∈ Finset.range 29, stT318 (i+1)) + stT318 30 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 29
    simpa using h
  have hprev := st318_p29
  have hstep := st318_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p31 : ((782570148679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT318 (i+1))
      = (∑ i ∈ Finset.range 30, stT318 (i+1)) + stT318 31 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 30
    simpa using h
  have hprev := st318_p30
  have hstep := st318_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p32 : ((-948879846073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT318 (i+1))
      = (∑ i ∈ Finset.range 31, stT318 (i+1)) + stT318 32 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 31
    simpa using h
  have hprev := st318_p31
  have hstep := st318_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p33 : ((154059669219/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT318 (i+1))
      = (∑ i ∈ Finset.range 32, stT318 (i+1)) + stT318 33 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 32
    simpa using h
  have hprev := st318_p32
  have hstep := st318_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p34 : ((-901430562027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT318 (i+1))
      = (∑ i ∈ Finset.range 33, stT318 (i+1)) + stT318 34 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 33
    simpa using h
  have hprev := st318_p33
  have hstep := st318_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p35 : ((157682182593/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT318 (i+1))
      = (∑ i ∈ Finset.range 34, stT318 (i+1)) + stT318 35 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 34
    simpa using h
  have hprev := st318_p34
  have hstep := st318_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p36 : ((-714192720889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT318 (i+1))
      = (∑ i ∈ Finset.range 35, stT318 (i+1)) + stT318 36 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 35
    simpa using h
  have hprev := st318_p35
  have hstep := st318_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p37 : ((-7147592123/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT318 (i+1))
      = (∑ i ∈ Finset.range 36, stT318 (i+1)) + stT318 37 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 36
    simpa using h
  have hprev := st318_p36
  have hstep := st318_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p38 : ((95875974589/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT318 (i+1))
      = (∑ i ∈ Finset.range 37, stT318 (i+1)) + stT318 38 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 37
    simpa using h
  have hprev := st318_p37
  have hstep := st318_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p39 : ((-410787217873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT318 (i+1))
      = (∑ i ∈ Finset.range 38, stT318 (i+1)) + stT318 39 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 38
    simpa using h
  have hprev := st318_p38
  have hstep := st318_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p40 : ((-8884267567/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT318 (i+1))
      = (∑ i ∈ Finset.range 39, stT318 (i+1)) + stT318 40 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 39
    simpa using h
  have hprev := st318_p39
  have hstep := st318_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p41 : ((847174024201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT318 (i+1))
      = (∑ i ∈ Finset.range 40, stT318 (i+1)) + stT318 41 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 40
    simpa using h
  have hprev := st318_p40
  have hstep := st318_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p42 : ((258863341957/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT318 (i+1))
      = (∑ i ∈ Finset.range 41, stT318 (i+1)) + stT318 42 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 41
    simpa using h
  have hprev := st318_p41
  have hstep := st318_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p43 : ((-19223397039/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT318 (i+1))
      = (∑ i ∈ Finset.range 42, stT318 (i+1)) + stT318 43 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 42
    simpa using h
  have hprev := st318_p42
  have hstep := st318_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p44 : ((-401393724849/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT318 (i+1))
      = (∑ i ∈ Finset.range 43, stT318 (i+1)) + stT318 44 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 43
    simpa using h
  have hprev := st318_p43
  have hstep := st318_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p45 : ((-465899814513/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT318 (i+1))
      = (∑ i ∈ Finset.range 44, stT318 (i+1)) + stT318 45 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 44
    simpa using h
  have hprev := st318_p44
  have hstep := st318_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p46 : ((-557764593849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT318 (i+1))
      = (∑ i ∈ Finset.range 45, stT318 (i+1)) + stT318 46 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 45
    simpa using h
  have hprev := st318_p45
  have hstep := st318_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p47 : ((88145604437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT318 (i+1))
      = (∑ i ∈ Finset.range 46, stT318 (i+1)) + stT318 47 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 46
    simpa using h
  have hprev := st318_p46
  have hstep := st318_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p48 : ((1615891783249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT318 (i+1))
      = (∑ i ∈ Finset.range 47, stT318 (i+1)) + stT318 48 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 47
    simpa using h
  have hprev := st318_p47
  have hstep := st318_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p49 : ((3015048506359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT318 (i+1))
      = (∑ i ∈ Finset.range 48, stT318 (i+1)) + stT318 49 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 48
    simpa using h
  have hprev := st318_p48
  have hstep := st318_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p50 : ((4346224575851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT318 (i+1))
      = (∑ i ∈ Finset.range 49, stT318 (i+1)) + stT318 50 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 49
    simpa using h
  have hprev := st318_p49
  have hstep := st318_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p51 : ((5657523783251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT318 (i+1))
      = (∑ i ∈ Finset.range 50, stT318 (i+1)) + stT318 51 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 50
    simpa using h
  have hprev := st318_p50
  have hstep := st318_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p52 : ((7001059879751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT318 (i+1))
      = (∑ i ∈ Finset.range 51, stT318 (i+1)) + stT318 52 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 51
    simpa using h
  have hprev := st318_p51
  have hstep := st318_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p53 : ((4187065273703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT318 (i+1))
      = (∑ i ∈ Finset.range 52, stT318 (i+1)) + stT318 53 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 52
    simpa using h
  have hprev := st318_p52
  have hstep := st318_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p54 : ((302119963691/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT318 (i+1))
      = (∑ i ∈ Finset.range 53, stT318 (i+1)) + stT318 54 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 53
    simpa using h
  have hprev := st318_p53
  have hstep := st318_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p55 : ((2128413310881/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT318 (i+1))
      = (∑ i ∈ Finset.range 54, stT318 (i+1)) + stT318 55 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 54
    simpa using h
  have hprev := st318_p54
  have hstep := st318_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p56 : ((10978057980903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT318 (i+1))
      = (∑ i ∈ Finset.range 55, stT318 (i+1)) + stT318 56 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 55
    simpa using h
  have hprev := st318_p55
  have hstep := st318_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p57 : ((32692442199/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT318 (i+1))
      = (∑ i ∈ Finset.range 56, stT318 (i+1)) + stT318 57 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 56
    simpa using h
  have hprev := st318_p56
  have hstep := st318_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p58 : ((185226123221/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT318 (i+1))
      = (∑ i ∈ Finset.range 57, stT318 (i+1)) + stT318 58 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 57
    simpa using h
  have hprev := st318_p57
  have hstep := st318_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p59 : ((403874163163/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT318 (i+1))
      = (∑ i ∈ Finset.range 58, stT318 (i+1)) + stT318 59 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 58
    simpa using h
  have hprev := st318_p58
  have hstep := st318_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p60 : ((781725740111/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT318 (i+1))
      = (∑ i ∈ Finset.range 59, stT318 (i+1)) + stT318 60 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 59
    simpa using h
  have hprev := st318_p59
  have hstep := st318_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p61 : ((4378380355339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT318 (i+1))
      = (∑ i ∈ Finset.range 60, stT318 (i+1)) + stT318 61 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 60
    simpa using h
  have hprev := st318_p60
  have hstep := st318_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p62 : ((4971359062251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT318 (i+1))
      = (∑ i ∈ Finset.range 61, stT318 (i+1)) + stT318 62 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 61
    simpa using h
  have hprev := st318_p61
  have hstep := st318_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p63 : ((497770760261/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT318 (i+1))
      = (∑ i ∈ Finset.range 62, stT318 (i+1)) + stT318 63 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 62
    simpa using h
  have hprev := st318_p62
  have hstep := st318_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p64 : ((4381630875749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT318 (i+1))
      = (∑ i ∈ Finset.range 63, stT318 (i+1)) + stT318 64 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 63
    simpa using h
  have hprev := st318_p63
  have hstep := st318_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p65 : ((4071429763733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT318 (i+1))
      = (∑ i ∈ Finset.range 64, stT318 (i+1)) + stT318 65 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 64
    simpa using h
  have hprev := st318_p64
  have hstep := st318_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p66 : ((4555160502023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT318 (i+1))
      = (∑ i ∈ Finset.range 65, stT318 (i+1)) + stT318 66 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 65
    simpa using h
  have hprev := st318_p65
  have hstep := st318_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p67 : ((4965193994161/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT318 (i+1))
      = (∑ i ∈ Finset.range 66, stT318 (i+1)) + stT318 67 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 66
    simpa using h
  have hprev := st318_p66
  have hstep := st318_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p68 : ((1806108030383/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT318 (i+1))
      = (∑ i ∈ Finset.range 67, stT318 (i+1)) + stT318 68 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 67
    simpa using h
  have hprev := st318_p67
  have hstep := st318_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p69 : ((8287684509657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT318 (i+1))
      = (∑ i ∈ Finset.range 68, stT318 (i+1)) + stT318 69 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 68
    simpa using h
  have hprev := st318_p68
  have hstep := st318_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p70 : ((9319965881189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT318 (i+1))
      = (∑ i ∈ Finset.range 69, stT318 (i+1)) + stT318 70 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 69
    simpa using h
  have hprev := st318_p69
  have hstep := st318_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p71 : ((1212547527909/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT318 (i+1))
      = (∑ i ∈ Finset.range 70, stT318 (i+1)) + stT318 71 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 70
    simpa using h
  have hprev := st318_p70
  have hstep := st318_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p72 : ((1065498840423/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT318 (i+1))
      = (∑ i ∈ Finset.range 71, stT318 (i+1)) + stT318 72 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 71
    simpa using h
  have hprev := st318_p71
  have hstep := st318_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p73 : ((8829801561519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT318 (i+1))
      = (∑ i ∈ Finset.range 72, stT318 (i+1)) + stT318 73 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 72
    simpa using h
  have hprev := st318_p72
  have hstep := st318_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p74 : ((9754926699267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT318 (i+1))
      = (∑ i ∈ Finset.range 73, stT318 (i+1)) + stT318 74 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 73
    simpa using h
  have hprev := st318_p73
  have hstep := st318_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p75 : ((2182209362837/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT318 (i+1))
      = (∑ i ∈ Finset.range 74, stT318 (i+1)) + stT318 75 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 74
    simpa using h
  have hprev := st318_p74
  have hstep := st318_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p76 : ((4377968584549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT318 (i+1))
      = (∑ i ∈ Finset.range 75, stT318 (i+1)) + stT318 76 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 75
    simpa using h
  have hprev := st318_p75
  have hstep := st318_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p77 : ((9709566610333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT318 (i+1))
      = (∑ i ∈ Finset.range 76, stT318 (i+1)) + stT318 77 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 76
    simpa using h
  have hprev := st318_p76
  have hstep := st318_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p78 : ((8659000584481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT318 (i+1))
      = (∑ i ∈ Finset.range 77, stT318 (i+1)) + stT318 78 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 77
    simpa using h
  have hprev := st318_p77
  have hstep := st318_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p79 : ((8968608775663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT318 (i+1))
      = (∑ i ∈ Finset.range 78, stT318 (i+1)) + stT318 79 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 78
    simpa using h
  have hprev := st318_p78
  have hstep := st318_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p80 : ((9580812341539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT318 (i+1))
      = (∑ i ∈ Finset.range 79, stT318 (i+1)) + stT318 80 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 79
    simpa using h
  have hprev := st318_p79
  have hstep := st318_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p81 : ((8488032578427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT318 (i+1))
      = (∑ i ∈ Finset.range 80, stT318 (i+1)) + stT318 81 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 80
    simpa using h
  have hprev := st318_p80
  have hstep := st318_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p82 : ((9412942772157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT318 (i+1))
      = (∑ i ∈ Finset.range 81, stT318 (i+1)) + stT318 82 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 81
    simpa using h
  have hprev := st318_p81
  have hstep := st318_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p83 : ((9109556442243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT318 (i+1))
      = (∑ i ∈ Finset.range 82, stT318 (i+1)) + stT318 83 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 82
    simpa using h
  have hprev := st318_p82
  have hstep := st318_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p84 : ((8697774711883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT318 (i+1))
      = (∑ i ∈ Finset.range 83, stT318 (i+1)) + stT318 84 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 83
    simpa using h
  have hprev := st318_p83
  have hstep := st318_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p85 : ((1923080447011/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT318 (i+1))
      = (∑ i ∈ Finset.range 84, stT318 (i+1)) + stT318 85 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 84
    simpa using h
  have hprev := st318_p84
  have hstep := st318_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p86 : ((8537096879943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT318 (i+1))
      = (∑ i ∈ Finset.range 85, stT318 (i+1)) + stT318 86 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 85
    simpa using h
  have hprev := st318_p85
  have hstep := st318_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p87 : ((9450790394487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT318 (i+1))
      = (∑ i ∈ Finset.range 86, stT318 (i+1)) + stT318 87 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 86
    simpa using h
  have hprev := st318_p86
  have hstep := st318_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p88 : ((8913896413883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT318 (i+1))
      = (∑ i ∈ Finset.range 87, stT318 (i+1)) + stT318 88 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 87
    simpa using h
  have hprev := st318_p87
  have hstep := st318_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p89 : ((4497166083117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT318 (i+1))
      = (∑ i ∈ Finset.range 88, stT318 (i+1)) + stT318 89 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 88
    simpa using h
  have hprev := st318_p88
  have hstep := st318_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p90 : ((4670619556947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT318 (i+1))
      = (∑ i ∈ Finset.range 89, stT318 (i+1)) + stT318 90 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 89
    simpa using h
  have hprev := st318_p89
  have hstep := st318_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p91 : ((8659641062039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT318 (i+1))
      = (∑ i ∈ Finset.range 90, stT318 (i+1)) + stT318 91 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 90
    simpa using h
  have hprev := st318_p90
  have hstep := st318_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p92 : ((9559480784951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT318 (i+1))
      = (∑ i ∈ Finset.range 91, stT318 (i+1)) + stT318 92 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 91
    simpa using h
  have hprev := st318_p91
  have hstep := st318_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p93 : ((342017409487/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT318 (i+1))
      = (∑ i ∈ Finset.range 92, stT318 (i+1)) + stT318 93 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 92
    simpa using h
  have hprev := st318_p92
  have hstep := st318_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p94 : ((4790694501731/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT318 (i+1))
      = (∑ i ∈ Finset.range 93, stT318 (i+1)) + stT318 94 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 93
    simpa using h
  have hprev := st318_p93
  have hstep := st318_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p95 : ((8587220482357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT318 (i+1))
      = (∑ i ∈ Finset.range 94, stT318 (i+1)) + stT318 95 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 94
    simpa using h
  have hprev := st318_p94
  have hstep := st318_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p96 : ((9511241861217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT318 (i+1))
      = (∑ i ∈ Finset.range 95, stT318 (i+1)) + stT318 96 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 95
    simpa using h
  have hprev := st318_p95
  have hstep := st318_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p97 : ((8668652091879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT318 (i+1))
      = (∑ i ∈ Finset.range 96, stT318 (i+1)) + stT318 97 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 96
    simpa using h
  have hprev := st318_p96
  have hstep := st318_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p98 : ((9433225029007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT318 (i+1))
      = (∑ i ∈ Finset.range 97, stT318 (i+1)) + stT318 98 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 97
    simpa using h
  have hprev := st318_p97
  have hstep := st318_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p99 : ((8732168812411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT318 (i+1))
      = (∑ i ∈ Finset.range 98, stT318 (i+1)) + stT318 99 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 98
    simpa using h
  have hprev := st318_p98
  have hstep := st318_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p100 : ((9389510155069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT318 (i+1))
      = (∑ i ∈ Finset.range 99, stT318 (i+1)) + stT318 100 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 99
    simpa using h
  have hprev := st318_p99
  have hstep := st318_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p101 : ((8752367422909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT318 (i+1))
      = (∑ i ∈ Finset.range 100, stT318 (i+1)) + stT318 101 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 100
    simpa using h
  have hprev := st318_p100
  have hstep := st318_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p102 : ((117408359423/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT318 (i+1))
      = (∑ i ∈ Finset.range 101, stT318 (i+1)) + stT318 102 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 101
    simpa using h
  have hprev := st318_p101
  have hstep := st318_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p103 : ((872635806261/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT318 (i+1))
      = (∑ i ∈ Finset.range 102, stT318 (i+1)) + stT318 103 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 102
    simpa using h
  have hprev := st318_p102
  have hstep := st318_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p104 : ((943756685313/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT318 (i+1))
      = (∑ i ∈ Finset.range 103, stT318 (i+1)) + stT318 104 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 103
    simpa using h
  have hprev := st318_p103
  have hstep := st318_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p105 : ((4333466482933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT318 (i+1))
      = (∑ i ∈ Finset.range 104, stT318 (i+1)) + stT318 105 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 104
    simpa using h
  have hprev := st318_p104
  have hstep := st318_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p106 : ((2375806708499/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT318 (i+1))
      = (∑ i ∈ Finset.range 105, stT318 (i+1)) + stT318 106 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 105
    simpa using h
  have hprev := st318_p105
  have hstep := st318_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p107 : ((8604531684267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT318 (i+1))
      = (∑ i ∈ Finset.range 106, stT318 (i+1)) + stT318 107 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 106
    simpa using h
  have hprev := st318_p106
  have hstep := st318_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p108 : ((9548585536767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT318 (i+1))
      = (∑ i ∈ Finset.range 107, stT318 (i+1)) + stT318 108 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 107
    simpa using h
  have hprev := st318_p107
  have hstep := st318_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p109 : ((1073849007589/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT318 (i+1))
      = (∑ i ∈ Finset.range 108, stT318 (i+1)) + stT318 109 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 108
    simpa using h
  have hprev := st318_p108
  have hstep := st318_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p110 : ((951358976933/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT318 (i+1))
      = (∑ i ∈ Finset.range 109, stT318 (i+1)) + stT318 110 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 109
    simpa using h
  have hprev := st318_p109
  have hstep := st318_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p111 : ((4344341123239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT318 (i+1))
      = (∑ i ∈ Finset.range 110, stT318 (i+1)) + stT318 111 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 110
    simpa using h
  have hprev := st318_p110
  have hstep := st318_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p112 : ((2335502680069/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT318 (i+1))
      = (∑ i ∈ Finset.range 111, stT318 (i+1)) + stT318 112 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 111
    simpa using h
  have hprev := st318_p111
  have hstep := st318_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p113 : ((558364962759/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT318 (i+1))
      = (∑ i ∈ Finset.range 112, stT318 (i+1)) + stT318 113 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 112
    simpa using h
  have hprev := st318_p112
  have hstep := st318_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p114 : ((9035516008329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT318 (i+1))
      = (∑ i ∈ Finset.range 113, stT318 (i+1)) + stT318 114 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 113
    simpa using h
  have hprev := st318_p113
  have hstep := st318_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p115 : ((9271004040961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT318 (i+1))
      = (∑ i ∈ Finset.range 114, stT318 (i+1)) + stT318 115 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 114
    simpa using h
  have hprev := st318_p114
  have hstep := st318_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p116 : ((1742728230963/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT318 (i+1))
      = (∑ i ∈ Finset.range 115, stT318 (i+1)) + stT318 116 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 115
    simpa using h
  have hprev := st318_p115
  have hstep := st318_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p117 : ((1903617486763/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT318 (i+1))
      = (∑ i ∈ Finset.range 116, stT318 (i+1)) + stT318 117 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 116
    simpa using h
  have hprev := st318_p116
  have hstep := st318_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p118 : ((430017896557/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT318 (i+1))
      = (∑ i ∈ Finset.range 117, stT318 (i+1)) + stT318 118 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 117
    simpa using h
  have hprev := st318_p117
  have hstep := st318_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p119 : ((2363050345259/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT318 (i+1))
      = (∑ i ∈ Finset.range 118, stT318 (i+1)) + stT318 119 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 118
    simpa using h
  have hprev := st318_p118
  have hstep := st318_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p120 : ((8855560762759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT318 (i+1))
      = (∑ i ∈ Finset.range 119, stT318 (i+1)) + stT318 120 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 119
    simpa using h
  have hprev := st318_p119
  have hstep := st318_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p121 : ((9044629664599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT318 (i+1))
      = (∑ i ∈ Finset.range 120, stT318 (i+1)) + stT318 121 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 120
    simpa using h
  have hprev := st318_p120
  have hstep := st318_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p122 : ((372990536673/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT318 (i+1))
      = (∑ i ∈ Finset.range 121, stT318 (i+1)) + stT318 122 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 121
    simpa using h
  have hprev := st318_p121
  have hstep := st318_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p123 : ((345645770917/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT318 (i+1))
      = (∑ i ∈ Finset.range 122, stT318 (i+1)) + stT318 123 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 122
    simpa using h
  have hprev := st318_p122
  have hstep := st318_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p124 : ((9529816434109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT318 (i+1))
      = (∑ i ∈ Finset.range 123, stT318 (i+1)) + stT318 124 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 123
    simpa using h
  have hprev := st318_p123
  have hstep := st318_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p125 : ((8721864416433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT318 (i+1))
      = (∑ i ∈ Finset.range 124, stT318 (i+1)) + stT318 125 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 124
    simpa using h
  have hprev := st318_p124
  have hstep := st318_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p126 : ((9164045959193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT318 (i+1))
      = (∑ i ∈ Finset.range 125, stT318 (i+1)) + stT318 126 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 125
    simpa using h
  have hprev := st318_p125
  have hstep := st318_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p127 : ((1851968450177/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT318 (i+1))
      = (∑ i ∈ Finset.range 126, stT318 (i+1)) + stT318 127 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 126
    simpa using h
  have hprev := st318_p126
  have hstep := st318_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p128 : ((8653572073141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT318 (i+1))
      = (∑ i ∈ Finset.range 127, stT318 (i+1)) + stT318 128 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 127
    simpa using h
  have hprev := st318_p127
  have hstep := st318_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p129 : ((9524280774341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT318 (i+1))
      = (∑ i ∈ Finset.range 128, stT318 (i+1)) + stT318 129 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 128
    simpa using h
  have hprev := st318_p128
  have hstep := st318_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p130 : ((175418636467/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT318 (i+1))
      = (∑ i ∈ Finset.range 129, stT318 (i+1)) + stT318 130 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 129
    simpa using h
  have hprev := st318_p129
  have hstep := st318_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p131 : ((4526248895159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT318 (i+1))
      = (∑ i ∈ Finset.range 130, stT318 (i+1)) + stT318 131 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 130
    simpa using h
  have hprev := st318_p130
  have hstep := st318_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p132 : ((4693712416747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT318 (i+1))
      = (∑ i ∈ Finset.range 131, stT318 (i+1)) + stT318 132 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 131
    simpa using h
  have hprev := st318_p131
  have hstep := st318_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p133 : ((4300328888827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT318 (i+1))
      = (∑ i ∈ Finset.range 132, stT318 (i+1)) + stT318 133 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 132
    simpa using h
  have hprev := st318_p132
  have hstep := st318_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p134 : ((4709545752031/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT318 (i+1))
      = (∑ i ∈ Finset.range 133, stT318 (i+1)) + stT318 134 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 133
    simpa using h
  have hprev := st318_p133
  have hstep := st318_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p135 : ((1806141915869/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT318 (i+1))
      = (∑ i ∈ Finset.range 134, stT318 (i+1)) + stT318 135 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 134
    simpa using h
  have hprev := st318_p134
  have hstep := st318_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p136 : ((8755473191191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT318 (i+1))
      = (∑ i ∈ Finset.range 135, stT318 (i+1)) + stT318 136 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 135
    simpa using h
  have hprev := st318_p135
  have hstep := st318_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p137 : ((953116697913/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT318 (i+1))
      = (∑ i ∈ Finset.range 136, stT318 (i+1)) + stT318 137 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 136
    simpa using h
  have hprev := st318_p136
  have hstep := st318_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p138 : ((8745908785597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT318 (i+1))
      = (∑ i ∈ Finset.range 137, stT318 (i+1)) + stT318 138 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 137
    simpa using h
  have hprev := st318_p137
  have hstep := st318_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p139 : ((9019574947421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT318 (i+1))
      = (∑ i ∈ Finset.range 138, stT318 (i+1)) + stT318 139 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 138
    simpa using h
  have hprev := st318_p138
  have hstep := st318_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p140 : ((9449204757551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT318 (i+1))
      = (∑ i ∈ Finset.range 139, stT318 (i+1)) + stT318 140 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 139
    simpa using h
  have hprev := st318_p139
  have hstep := st318_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p141 : ((8617612501479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT318 (i+1))
      = (∑ i ∈ Finset.range 140, stT318 (i+1)) + stT318 141 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 140
    simpa using h
  have hprev := st318_p140
  have hstep := st318_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p142 : ((9240022979007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT318 (i+1))
      = (∑ i ∈ Finset.range 141, stT318 (i+1)) + stT318 142 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 141
    simpa using h
  have hprev := st318_p141
  have hstep := st318_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p143 : ((9301985166239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT318 (i+1))
      = (∑ i ∈ Finset.range 142, stT318 (i+1)) + stT318 143 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 142
    simpa using h
  have hprev := st318_p142
  have hstep := st318_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p144 : ((8600747105249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT318 (i+1))
      = (∑ i ∈ Finset.range 143, stT318 (i+1)) + stT318 144 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 143
    simpa using h
  have hprev := st318_p143
  have hstep := st318_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p145 : ((9374943659927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT318 (i+1))
      = (∑ i ∈ Finset.range 144, stT318 (i+1)) + stT318 145 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 144
    simpa using h
  have hprev := st318_p144
  have hstep := st318_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p146 : ((1834845371913/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT318 (i+1))
      = (∑ i ∈ Finset.range 145, stT318 (i+1)) + stT318 146 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 145
    simpa using h
  have hprev := st318_p145
  have hstep := st318_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p147 : ((2156631556857/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT318 (i+1))
      = (∑ i ∈ Finset.range 146, stT318 (i+1)) + stT318 147 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 146
    simpa using h
  have hprev := st318_p146
  have hstep := st318_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p148 : ((2360071783881/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT318 (i+1))
      = (∑ i ∈ Finset.range 147, stT318 (i+1)) + stT318 148 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 147
    simpa using h
  have hprev := st318_p147
  have hstep := st318_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p149 : ((2274727471049/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT318 (i+1))
      = (∑ i ∈ Finset.range 148, stT318 (i+1)) + stT318 149 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 148
    simpa using h
  have hprev := st318_p148
  have hstep := st318_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p150 : ((4324042165817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT318 (i+1))
      = (∑ i ∈ Finset.range 149, stT318 (i+1)) + stT318 150 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 149
    simpa using h
  have hprev := st318_p149
  have hstep := st318_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p151 : ((4730525609771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT318 (i+1))
      = (∑ i ∈ Finset.range 150, stT318 (i+1)) + stT318 151 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 150
    simpa using h
  have hprev := st318_p150
  have hstep := st318_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p152 : ((4541198402627/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT318 (i+1))
      = (∑ i ∈ Finset.range 151, stT318 (i+1)) + stT318 152 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 151
    simpa using h
  have hprev := st318_p151
  have hstep := st318_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p153 : ((8645543567533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT318 (i+1))
      = (∑ i ∈ Finset.range 152, stT318 (i+1)) + stT318 153 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 152
    simpa using h
  have hprev := st318_p152
  have hstep := st318_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p154 : ((9449318779653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT318 (i+1))
      = (∑ i ∈ Finset.range 153, stT318 (i+1)) + stT318 154 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 153
    simpa using h
  have hprev := st318_p153
  have hstep := st318_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p155 : ((9123482948013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT318 (i+1))
      = (∑ i ∈ Finset.range 154, stT318 (i+1)) + stT318 155 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 154
    simpa using h
  have hprev := st318_p154
  have hstep := st318_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p156 : ((8620605139759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT318 (i+1))
      = (∑ i ∈ Finset.range 155, stT318 (i+1)) + stT318 156 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 155
    simpa using h
  have hprev := st318_p155
  have hstep := st318_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p157 : ((9399754953237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT318 (i+1))
      = (∑ i ∈ Finset.range 156, stT318 (i+1)) + stT318 157 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 156
    simpa using h
  have hprev := st318_p156
  have hstep := st318_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p158 : ((9217967563563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT318 (i+1))
      = (∑ i ∈ Finset.range 157, stT318 (i+1)) + stT318 158 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 157
    simpa using h
  have hprev := st318_p157
  have hstep := st318_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p159 : ((8594295609723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT318 (i+1))
      = (∑ i ∈ Finset.range 158, stT318 (i+1)) + stT318 159 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 158
    simpa using h
  have hprev := st318_p158
  have hstep := st318_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p160 : ((4647377382267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT318 (i+1))
      = (∑ i ∈ Finset.range 159, stT318 (i+1)) + stT318 160 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 159
    simpa using h
  have hprev := st318_p159
  have hstep := st318_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p161 : ((4675445919917/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT318 (i+1))
      = (∑ i ∈ Finset.range 160, stT318 (i+1)) + stT318 161 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 160
    simpa using h
  have hprev := st318_p160
  have hstep := st318_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p162 : ((4303369096117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT318 (i+1))
      = (∑ i ∈ Finset.range 161, stT318 (i+1)) + stT318 162 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 161
    simpa using h
  have hprev := st318_p161
  have hstep := st318_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p163 : ((4559501382197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT318 (i+1))
      = (∑ i ∈ Finset.range 162, stT318 (i+1)) + stT318 163 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 162
    simpa using h
  have hprev := st318_p162
  have hstep := st318_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p164 : ((4741011806193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT318 (i+1))
      = (∑ i ∈ Finset.range 163, stT318 (i+1)) + stT318 164 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 163
    simpa using h
  have hprev := st318_p163
  have hstep := st318_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p165 : ((4354583586569/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT318 (i+1))
      = (∑ i ∈ Finset.range 164, stT318 (i+1)) + stT318 165 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 164
    simpa using h
  have hprev := st318_p164
  have hstep := st318_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p166 : ((2221386233047/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT318 (i+1))
      = (∑ i ∈ Finset.range 165, stT318 (i+1)) + stT318 166 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 165
    simpa using h
  have hprev := st318_p165
  have hstep := st318_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p167 : ((1192197184733/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT318 (i+1))
      = (∑ i ∈ Finset.range 166, stT318 (i+1)) + stT318 167 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 166
    simpa using h
  have hprev := st318_p166
  have hstep := st318_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p168 : ((4467490519473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT318 (i+1))
      = (∑ i ∈ Finset.range 167, stT318 (i+1)) + stT318 168 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 167
    simpa using h
  have hprev := st318_p167
  have hstep := st318_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p169 : ((4332633555939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT318 (i+1))
      = (∑ i ∈ Finset.range 168, stT318 (i+1)) + stT318 169 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 168
    simpa using h
  have hprev := st318_p168
  have hstep := st318_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p170 : ((4715542250349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT318 (i+1))
      = (∑ i ∈ Finset.range 169, stT318 (i+1)) + stT318 170 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 169
    simpa using h
  have hprev := st318_p169
  have hstep := st318_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p171 : ((4624066826309/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT318 (i+1))
      = (∑ i ∈ Finset.range 170, stT318 (i+1)) + stT318 171 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 170
    simpa using h
  have hprev := st318_p170
  have hstep := st318_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p172 : ((2147054708977/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT318 (i+1))
      = (∑ i ∈ Finset.range 171, stT318 (i+1)) + stT318 172 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 171
    simpa using h
  have hprev := st318_p171
  have hstep := st318_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p173 : ((9132259774783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT318 (i+1))
      = (∑ i ∈ Finset.range 172, stT318 (i+1)) + stT318 173 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 172
    simpa using h
  have hprev := st318_p172
  have hstep := st318_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p174 : ((9503028070329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT318 (i+1))
      = (∑ i ∈ Finset.range 173, stT318 (i+1)) + stT318 174 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 173
    simpa using h
  have hprev := st318_p173
  have hstep := st318_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p175 : ((8772348610787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT318 (i+1))
      = (∑ i ∈ Finset.range 174, stT318 (i+1)) + stT318 175 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 174
    simpa using h
  have hprev := st318_p174
  have hstep := st318_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p176 : ((4379197703859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT318 (i+1))
      = (∑ i ∈ Finset.range 175, stT318 (i+1)) + stT318 176 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 175
    simpa using h
  have hprev := st318_p175
  have hstep := st318_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p177 : ((593316028941/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT318 (i+1))
      = (∑ i ∈ Finset.range 176, stT318 (i+1)) + stT318 177 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 176
    simpa using h
  have hprev := st318_p176
  have hstep := st318_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p178 : ((2294574686127/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT318 (i+1))
      = (∑ i ∈ Finset.range 177, stT318 (i+1)) + stT318 178 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 177
    simpa using h
  have hprev := st318_p177
  have hstep := st318_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p179 : ((1072562522393/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT318 (i+1))
      = (∑ i ∈ Finset.range 178, stT318 (i+1)) + stT318 179 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 178
    simpa using h
  have hprev := st318_p178
  have hstep := st318_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p180 : ((1142227872823/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT318 (i+1))
      = (∑ i ∈ Finset.range 179, stT318 (i+1)) + stT318 180 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 179
    simpa using h
  have hprev := st318_p179
  have hstep := st318_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p181 : ((2379181504653/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT318 (i+1))
      = (∑ i ∈ Finset.range 180, stT318 (i+1)) + stT318 181 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 180
    simpa using h
  have hprev := st318_p180
  have hstep := st318_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p182 : ((1102663067639/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT318 (i+1))
      = (∑ i ∈ Finset.range 181, stT318 (i+1)) + stT318 182 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 181
    simpa using h
  have hprev := st318_p181
  have hstep := st318_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p183 : ((2171843444399/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT318 (i+1))
      = (∑ i ∈ Finset.range 182, stT318 (i+1)) + stT318 183 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 182
    simpa using h
  have hprev := st318_p182
  have hstep := st318_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p184 : ((4712181544657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT318 (i+1))
      = (∑ i ∈ Finset.range 183, stT318 (i+1)) + stT318 184 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 183
    simpa using h
  have hprev := st318_p183
  have hstep := st318_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p185 : ((1165859381343/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT318 (i+1))
      = (∑ i ∈ Finset.range 184, stT318 (i+1)) + stT318 185 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 184
    simpa using h
  have hprev := st318_p184
  have hstep := st318_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p186 : ((2155347458409/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT318 (i+1))
      = (∑ i ∈ Finset.range 185, stT318 (i+1)) + stT318 186 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 185
    simpa using h
  have hprev := st318_p185
  have hstep := st318_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p187 : ((2228317252111/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT318 (i+1))
      = (∑ i ∈ Finset.range 186, stT318 (i+1)) + stT318 187 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 186
    simpa using h
  have hprev := st318_p186
  have hstep := st318_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p188 : ((2385070859431/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT318 (i+1))
      = (∑ i ∈ Finset.range 187, stT318 (i+1)) + stT318 188 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 187
    simpa using h
  have hprev := st318_p187
  have hstep := st318_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p189 : ((9098784255051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT318 (i+1))
      = (∑ i ∈ Finset.range 188, stT318 (i+1)) + stT318 189 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 188
    simpa using h
  have hprev := st318_p188
  have hstep := st318_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p190 : ((857255733667/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT318 (i+1))
      = (∑ i ∈ Finset.range 189, stT318 (i+1)) + stT318 190 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 189
    simpa using h
  have hprev := st318_p189
  have hstep := st318_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p191 : ((4559925672247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT318 (i+1))
      = (∑ i ∈ Finset.range 190, stT318 (i+1)) + stT318 191 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 190
    simpa using h
  have hprev := st318_p190
  have hstep := st318_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p192 : ((4770467750879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT318 (i+1))
      = (∑ i ∈ Finset.range 191, stT318 (i+1)) + stT318 192 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 191
    simpa using h
  have hprev := st318_p191
  have hstep := st318_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p193 : ((4462100735927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT318 (i+1))
      = (∑ i ∈ Finset.range 192, stT318 (i+1)) + stT318 193 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 192
    simpa using h
  have hprev := st318_p192
  have hstep := st318_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p194 : ((4299698410127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT318 (i+1))
      = (∑ i ∈ Finset.range 193, stT318 (i+1)) + stT318 194 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 193
    simpa using h
  have hprev := st318_p193
  have hstep := st318_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p195 : ((925745832273/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT318 (i+1))
      = (∑ i ∈ Finset.range 194, stT318 (i+1)) + stT318 195 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 194
    simpa using h
  have hprev := st318_p194
  have hstep := st318_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p196 : ((1900378044231/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT318 (i+1))
      = (∑ i ∈ Finset.range 195, stT318 (i+1)) + stT318 196 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 195
    simpa using h
  have hprev := st318_p195
  have hstep := st318_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p197 : ((8821555938081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT318 (i+1))
      = (∑ i ∈ Finset.range 196, stT318 (i+1)) + stT318 197 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 196
    simpa using h
  have hprev := st318_p196
  have hstep := st318_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p198 : ((8637070270101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT318 (i+1))
      = (∑ i ∈ Finset.range 197, stT318 (i+1)) + stT318 198 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 197
    simpa using h
  have hprev := st318_p197
  have hstep := st318_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p199 : ((291468950793/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT318 (i+1))
      = (∑ i ∈ Finset.range 198, stT318 (i+1)) + stT318 199 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 198
    simpa using h
  have hprev := st318_p198
  have hstep := st318_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p200 : ((4736510846529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT318 (i+1))
      = (∑ i ∈ Finset.range 199, stT318 (i+1)) + stT318 200 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 199
    simpa using h
  have hprev := st318_p199
  have hstep := st318_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p201 : ((1097584843321/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT318 (i+1))
      = (∑ i ∈ Finset.range 200, stT318 (i+1)) + stT318 201 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 200
    simpa using h
  have hprev := st318_p200
  have hstep := st318_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p202 : ((865084310403/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT318 (i+1))
      = (∑ i ∈ Finset.range 201, stT318 (i+1)) + stT318 202 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 201
    simpa using h
  have hprev := st318_p201
  have hstep := st318_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p203 : ((2335135283427/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT318 (i+1))
      = (∑ i ∈ Finset.range 202, stT318 (i+1)) + stT318 203 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 202
    simpa using h
  have hprev := st318_p202
  have hstep := st318_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p204 : ((2368871179257/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT318 (i+1))
      = (∑ i ∈ Finset.range 203, stT318 (i+1)) + stT318 204 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 203
    simpa using h
  have hprev := st318_p203
  have hstep := st318_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p205 : ((4396151629741/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT318 (i+1))
      = (∑ i ∈ Finset.range 204, stT318 (i+1)) + stT318 205 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 204
    simpa using h
  have hprev := st318_p204
  have hstep := st318_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p206 : ((863124065417/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT318 (i+1))
      = (∑ i ∈ Finset.range 205, stT318 (i+1)) + stT318 206 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 205
    simpa using h
  have hprev := st318_p205
  have hstep := st318_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p207 : ((4651067173037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT318 (i+1))
      = (∑ i ∈ Finset.range 206, stT318 (i+1)) + stT318 207 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 206
    simpa using h
  have hprev := st318_p206
  have hstep := st318_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p208 : ((9508483439449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT318 (i+1))
      = (∑ i ∈ Finset.range 207, stT318 (i+1)) + stT318 208 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 207
    simpa using h
  have hprev := st318_p207
  have hstep := st318_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p209 : ((553633528439/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT318 (i+1))
      = (∑ i ∈ Finset.range 208, stT318 (i+1)) + stT318 209 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 208
    simpa using h
  have hprev := st318_p208
  have hstep := st318_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p210 : ((134200790933/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT318 (i+1))
      = (∑ i ∈ Finset.range 209, stT318 (i+1)) + stT318 210 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 209
    simpa using h
  have hprev := st318_p209
  have hstep := st318_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p211 : ((460268994391/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT318 (i+1))
      = (∑ i ∈ Finset.range 210, stT318 (i+1)) + stT318 211 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 210
    simpa using h
  have hprev := st318_p210
  have hstep := st318_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p212 : ((4775705326339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT318 (i+1))
      = (∑ i ∈ Finset.range 211, stT318 (i+1)) + stT318 212 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 211
    simpa using h
  have hprev := st318_p211
  have hstep := st318_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p213 : ((4493392384181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT318 (i+1))
      = (∑ i ∈ Finset.range 212, stT318 (i+1)) + stT318 213 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 212
    simpa using h
  have hprev := st318_p212
  have hstep := st318_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p214 : ((4277438680163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT318 (i+1))
      = (∑ i ∈ Finset.range 213, stT318 (i+1)) + stT318 214 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 213
    simpa using h
  have hprev := st318_p213
  have hstep := st318_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p215 : ((141303784001/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT318 (i+1))
      = (∑ i ∈ Finset.range 214, stT318 (i+1)) + stT318 215 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 214
    simpa using h
  have hprev := st318_p214
  have hstep := st318_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p216 : ((9562206057589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT318 (i+1))
      = (∑ i ∈ Finset.range 215, stT318 (i+1)) + stT318 216 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 215
    simpa using h
  have hprev := st318_p215
  have hstep := st318_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p217 : ((1147241957833/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT318 (i+1))
      = (∑ i ∈ Finset.range 216, stT318 (i+1)) + stT318 217 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 216
    simpa using h
  have hprev := st318_p216
  have hstep := st318_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p218 : ((536324701433/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT318 (i+1))
      = (∑ i ∈ Finset.range 217, stT318 (i+1)) + stT318 218 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 217
    simpa using h
  have hprev := st318_p217
  have hstep := st318_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p219 : ((4415092017659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT318 (i+1))
      = (∑ i ∈ Finset.range 218, stT318 (i+1)) + stT318 219 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 218
    simpa using h
  have hprev := st318_p218
  have hstep := st318_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p220 : ((474122162573/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT318 (i+1))
      = (∑ i ∈ Finset.range 219, stT318 (i+1)) + stT318 220 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 219
    simpa using h
  have hprev := st318_p219
  have hstep := st318_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p221 : ((2349324748453/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT318 (i+1))
      = (∑ i ∈ Finset.range 220, stT318 (i+1)) + stT318 221 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 220
    simpa using h
  have hprev := st318_p220
  have hstep := st318_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p222 : ((8726098368607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT318 (i+1))
      = (∑ i ∈ Finset.range 221, stT318 (i+1)) + stT318 222 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 221
    simpa using h
  have hprev := st318_p221
  have hstep := st318_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p223 : ((8626016497507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT318 (i+1))
      = (∑ i ∈ Finset.range 222, stT318 (i+1)) + stT318 223 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 222
    simpa using h
  have hprev := st318_p222
  have hstep := st318_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p224 : ((9264677224087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT318 (i+1))
      = (∑ i ∈ Finset.range 223, stT318 (i+1)) + stT318 224 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 223
    simpa using h
  have hprev := st318_p223
  have hstep := st318_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p225 : ((9555896266201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT318 (i+1))
      = (∑ i ∈ Finset.range 224, stT318 (i+1)) + stT318 225 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 224
    simpa using h
  have hprev := st318_p224
  have hstep := st318_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p226 : ((1802334582063/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT318 (i+1))
      = (∑ i ∈ Finset.range 225, stT318 (i+1)) + stT318 226 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 225
    simpa using h
  have hprev := st318_p225
  have hstep := st318_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p227 : ((8545011220811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT318 (i+1))
      = (∑ i ∈ Finset.range 226, stT318 (i+1)) + stT318 227 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 226
    simpa using h
  have hprev := st318_p226
  have hstep := st318_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p228 : ((1785754767513/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT318 (i+1))
      = (∑ i ∈ Finset.range 227, stT318 (i+1)) + stT318 228 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 227
    simpa using h
  have hprev := st318_p227
  have hstep := st318_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p229 : ((1905367451239/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT318 (i+1))
      = (∑ i ∈ Finset.range 228, stT318 (i+1)) + stT318 229 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 228
    simpa using h
  have hprev := st318_p228
  have hstep := st318_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p230 : ((9361132173371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT318 (i+1))
      = (∑ i ∈ Finset.range 229, stT318 (i+1)) + stT318 230 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 229
    simpa using h
  have hprev := st318_p229
  have hstep := st318_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p231 : ((1740881713951/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT318 (i+1))
      = (∑ i ∈ Finset.range 230, stT318 (i+1)) + stT318 231 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 230
    simpa using h
  have hprev := st318_p230
  have hstep := st318_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p232 : ((4308176853631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT318 (i+1))
      = (∑ i ∈ Finset.range 231, stT318 (i+1)) + stT318 232 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 231
    simpa using h
  have hprev := st318_p231
  have hstep := st318_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p233 : ((9234457095157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT318 (i+1))
      = (∑ i ∈ Finset.range 232, stT318 (i+1)) + stT318 233 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 232
    simpa using h
  have hprev := st318_p232
  have hstep := st318_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p234 : ((9574057444237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT318 (i+1))
      = (∑ i ∈ Finset.range 233, stT318 (i+1)) + stT318 234 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 233
    simpa using h
  have hprev := st318_p233
  have hstep := st318_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p235 : ((4550824631357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT318 (i+1))
      = (∑ i ∈ Finset.range 234, stT318 (i+1)) + stT318 235 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 234
    simpa using h
  have hprev := st318_p234
  have hstep := st318_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p236 : ((8560411278289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT318 (i+1))
      = (∑ i ∈ Finset.range 235, stT318 (i+1)) + stT318 236 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 235
    simpa using h
  have hprev := st318_p235
  have hstep := st318_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p237 : ((8791019965531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT318 (i+1))
      = (∑ i ∈ Finset.range 236, stT318 (i+1)) + stT318 237 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 236
    simpa using h
  have hprev := st318_p236
  have hstep := st318_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p238 : ((1886717757011/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT318 (i+1))
      = (∑ i ∈ Finset.range 237, stT318 (i+1)) + stT318 238 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 237
    simpa using h
  have hprev := st318_p237
  have hstep := st318_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p239 : ((9502136349367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT318 (i+1))
      = (∑ i ∈ Finset.range 238, stT318 (i+1)) + stT318 239 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 238
    simpa using h
  have hprev := st318_p238
  have hstep := st318_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p240 : ((8895551550799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT318 (i+1))
      = (∑ i ∈ Finset.range 239, stT318 (i+1)) + stT318 240 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 239
    simpa using h
  have hprev := st318_p239
  have hstep := st318_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p241 : ((4266458140961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT318 (i+1))
      = (∑ i ∈ Finset.range 240, stT318 (i+1)) + stT318 241 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 240
    simpa using h
  have hprev := st318_p240
  have hstep := st318_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p242 : ((4478101836133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT318 (i+1))
      = (∑ i ∈ Finset.range 241, stT318 (i+1)) + stT318 242 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 241
    simpa using h
  have hprev := st318_p241
  have hstep := st318_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p243 : ((4765553816383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT318 (i+1))
      = (∑ i ∈ Finset.range 242, stT318 (i+1)) + stT318 243 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 242
    simpa using h
  have hprev := st318_p242
  have hstep := st318_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p244 : ((9407224793231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT318 (i+1))
      = (∑ i ∈ Finset.range 243, stT318 (i+1)) + stT318 244 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 243
    simpa using h
  have hprev := st318_p243
  have hstep := st318_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p245 : ((2192526655403/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT318 (i+1))
      = (∑ i ∈ Finset.range 244, stT318 (i+1)) + stT318 245 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 244
    simpa using h
  have hprev := st318_p244
  have hstep := st318_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p246 : ((1710160999823/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT318 (i+1))
      = (∑ i ∈ Finset.range 245, stT318 (i+1)) + stT318 246 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 245
    simpa using h
  have hprev := st318_p245
  have hstep := st318_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p247 : ((72513729567/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT318 (i+1))
      = (∑ i ∈ Finset.range 246, stT318 (i+1)) + stT318 247 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 246
    simpa using h
  have hprev := st318_p246
  have hstep := st318_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p248 : ((76547813447/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT318 (i+1))
      = (∑ i ∈ Finset.range 247, stT318 (i+1)) + stT318 248 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 247
    simpa using h
  have hprev := st318_p247
  have hstep := st318_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p249 : ((93440093847/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT318 (i+1))
      = (∑ i ∈ Finset.range 248, stT318 (i+1)) + stT318 249 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 248
    simpa using h
  have hprev := st318_p248
  have hstep := st318_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p250 : ((435642812203/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT318 (i+1))
      = (∑ i ∈ Finset.range 249, stT318 (i+1)) + stT318 250 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 249
    simpa using h
  have hprev := st318_p249
  have hstep := st318_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p251 : ((214136300333/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT318 (i+1))
      = (∑ i ∈ Finset.range 250, stT318 (i+1)) + stT318 251 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 250
    simpa using h
  have hprev := st318_p250
  have hstep := st318_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p252 : ((113813059483/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT318 (i+1))
      = (∑ i ∈ Finset.range 251, stT318 (i+1)) + stT318 252 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 251
    simpa using h
  have hprev := st318_p251
  have hstep := st318_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p253 : ((2394677904989/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT318 (i+1))
      = (∑ i ∈ Finset.range 252, stT318 (i+1)) + stT318 253 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 252
    simpa using h
  have hprev := st318_p252
  have hstep := st318_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p254 : ((2333424081629/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT318 (i+1))
      = (∑ i ∈ Finset.range 253, stT318 (i+1)) + stT318 254 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 253
    simpa using h
  have hprev := st318_p253
  have hstep := st318_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p255 : ((2177350024879/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT318 (i+1))
      = (∑ i ∈ Finset.range 254, stT318 (i+1)) + stT318 255 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 254
    simpa using h
  have hprev := st318_p254
  have hstep := st318_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p256 : ((4278445552751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT318 (i+1))
      = (∑ i ∈ Finset.range 255, stT318 (i+1)) + stT318 256 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 255
    simpa using h
  have hprev := st318_p255
  have hstep := st318_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p257 : ((4539735980693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT318 (i+1))
      = (∑ i ∈ Finset.range 256, stT318 (i+1)) + stT318 257 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 256
    simpa using h
  have hprev := st318_p256
  have hstep := st318_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p258 : ((4786092390383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT318 (i+1))
      = (∑ i ∈ Finset.range 257, stT318 (i+1)) + stT318 258 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 257
    simpa using h
  have hprev := st318_p257
  have hstep := st318_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p259 : ((2344622675749/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT318 (i+1))
      = (∑ i ∈ Finset.range 258, stT318 (i+1)) + stT318 259 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 258
    simpa using h
  have hprev := st318_p258
  have hstep := st318_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p260 : ((4379252928033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT318 (i+1))
      = (∑ i ∈ Finset.range 259, stT318 (i+1)) + stT318 260 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 259
    simpa using h
  have hprev := st318_p259
  have hstep := st318_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p261 : ((2132426369659/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT318 (i+1))
      = (∑ i ∈ Finset.range 260, stT318 (i+1)) + stT318 261 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 260
    simpa using h
  have hprev := st318_p260
  have hstep := st318_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p262 : ((179773498181/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT318 (i+1))
      = (∑ i ∈ Finset.range 261, stT318 (i+1)) + stT318 262 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 261
    simpa using h
  have hprev := st318_p261
  have hstep := st318_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p263 : ((238401884779/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT318 (i+1))
      = (∑ i ∈ Finset.range 262, stT318 (i+1)) + stT318 263 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 262
    simpa using h
  have hprev := st318_p262
  have hstep := st318_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p264 : ((946586701981/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT318 (i+1))
      = (∑ i ∈ Finset.range 263, stT318 (i+1)) + stT318 264 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 263
    simpa using h
  have hprev := st318_p263
  have hstep := st318_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p265 : ((4435633596229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT318 (i+1))
      = (∑ i ∈ Finset.range 264, stT318 (i+1)) + stT318 265 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 264
    simpa using h
  have hprev := st318_p264
  have hstep := st318_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p266 : ((4255643283529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT318 (i+1))
      = (∑ i ∈ Finset.range 265, stT318 (i+1)) + stT318 266 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 265
    simpa using h
  have hprev := st318_p265
  have hstep := st318_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p267 : ((2209836104637/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT318 (i+1))
      = (∑ i ∈ Finset.range 266, stT318 (i+1)) + stT318 267 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 266
    simpa using h
  have hprev := st318_p266
  have hstep := st318_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p268 : ((943983511851/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT318 (i+1))
      = (∑ i ∈ Finset.range 267, stT318 (i+1)) + stT318 268 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 267
    simpa using h
  have hprev := st318_p267
  have hstep := st318_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p269 : ((956244779951/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT318 (i+1))
      = (∑ i ∈ Finset.range 268, stT318 (i+1)) + stT318 269 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 268
    simpa using h
  have hprev := st318_p268
  have hstep := st318_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p270 : ((9057849557751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT318 (i+1))
      = (∑ i ∈ Finset.range 269, stT318 (i+1)) + stT318 270 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 269
    simpa using h
  have hprev := st318_p269
  have hstep := st318_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p271 : ((8550409137887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT318 (i+1))
      = (∑ i ∈ Finset.range 270, stT318 (i+1)) + stT318 271 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 270
    simpa using h
  have hprev := st318_p270
  have hstep := st318_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p272 : ((4330245901177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT318 (i+1))
      = (∑ i ∈ Finset.range 271, stT318 (i+1)) + stT318 272 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 271
    simpa using h
  have hprev := st318_p271
  have hstep := st318_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p273 : ((1850183353123/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT318 (i+1))
      = (∑ i ∈ Finset.range 272, stT318 (i+1)) + stT318 273 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 272
    simpa using h
  have hprev := st318_p272
  have hstep := st318_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p274 : ((9606393628733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT318 (i+1))
      = (∑ i ∈ Finset.range 273, stT318 (i+1)) + stT318 274 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 273
    simpa using h
  have hprev := st318_p273
  have hstep := st318_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p275 : ((4650946471861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT318 (i+1))
      = (∑ i ∈ Finset.range 274, stT318 (i+1)) + stT318 275 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 274
    simpa using h
  have hprev := st318_p274
  have hstep := st318_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p276 : ((4351860697321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT318 (i+1))
      = (∑ i ∈ Finset.range 275, stT318 (i+1)) + stT318 276 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 275
    simpa using h
  have hprev := st318_p275
  have hstep := st318_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p277 : ((2130380066009/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT318 (i+1))
      = (∑ i ∈ Finset.range 276, stT318 (i+1)) + stT318 277 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 276
    simpa using h
  have hprev := st318_p276
  have hstep := st318_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p278 : ((2241812025389/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT318 (i+1))
      = (∑ i ∈ Finset.range 277, stT318 (i+1)) + stT318 278 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 277
    simpa using h
  have hprev := st318_p277
  have hstep := st318_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p279 : ((237912484059/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT318 (i+1))
      = (∑ i ∈ Finset.range 278, stT318 (i+1)) + stT318 279 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 278
    simpa using h
  have hprev := st318_p278
  have hstep := st318_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p280 : ((1191351676611/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT318 (i+1))
      = (∑ i ∈ Finset.range 279, stT318 (i+1)) + stT318 280 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 279
    simpa using h
  have hprev := st318_p279
  have hstep := st318_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p281 : ((562282908093/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT318 (i+1))
      = (∑ i ∈ Finset.range 280, stT318 (i+1)) + stT318 281 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 280
    simpa using h
  have hprev := st318_p280
  have hstep := st318_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p282 : ((2132286722973/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT318 (i+1))
      = (∑ i ∈ Finset.range 281, stT318 (i+1)) + stT318 282 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 281
    simpa using h
  have hprev := st318_p281
  have hstep := st318_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p283 : ((173215002303/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT318 (i+1))
      = (∑ i ∈ Finset.range 282, stT318 (i+1)) + stT318 283 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 282
    simpa using h
  have hprev := st318_p282
  have hstep := st318_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p284 : ((461951293923/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT318 (i+1))
      = (∑ i ∈ Finset.range 283, stT318 (i+1)) + stT318 284 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 283
    simpa using h
  have hprev := st318_p283
  have hstep := st318_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p285 : ((2402719268561/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT318 (i+1))
      = (∑ i ∈ Finset.range 284, stT318 (i+1)) + stT318 285 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 284
    simpa using h
  have hprev := st318_p284
  have hstep := st318_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p286 : ((9361600209399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT318 (i+1))
      = (∑ i ∈ Finset.range 285, stT318 (i+1)) + stT318 286 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 285
    simpa using h
  have hprev := st318_p285
  have hstep := st318_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p287 : ((1754291149021/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT318 (i+1))
      = (∑ i ∈ Finset.range 286, stT318 (i+1)) + stT318 287 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 286
    simpa using h
  have hprev := st318_p286
  have hstep := st318_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p288 : ((8493808335257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT318 (i+1))
      = (∑ i ∈ Finset.range 287, stT318 (i+1)) + stT318 288 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 287
    simpa using h
  have hprev := st318_p287
  have hstep := st318_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p289 : ((8831565813437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT318 (i+1))
      = (∑ i ∈ Finset.range 288, stT318 (i+1)) + stT318 289 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 288
    simpa using h
  have hprev := st318_p288
  have hstep := st318_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p290 : ((9413030470217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT318 (i+1))
      = (∑ i ∈ Finset.range 289, stT318 (i+1)) + stT318 290 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 289
    simpa using h
  have hprev := st318_p289
  have hstep := st318_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p291 : ((9606662667737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT318 (i+1))
      = (∑ i ∈ Finset.range 290, stT318 (i+1)) + stT318 291 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 290
    simpa using h
  have hprev := st318_p290
  have hstep := st318_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p292 : ((9205914184143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT318 (i+1))
      = (∑ i ∈ Finset.range 291, stT318 (i+1)) + stT318 292 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 291
    simpa using h
  have hprev := st318_p291
  have hstep := st318_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p293 : ((8642903382517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT318 (i+1))
      = (∑ i ∈ Finset.range 292, stT318 (i+1)) + stT318 293 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 292
    simpa using h
  have hprev := st318_p292
  have hstep := st318_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p294 : ((8517412490053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT318 (i+1))
      = (∑ i ∈ Finset.range 293, stT318 (i+1)) + stT318 294 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 293
    simpa using h
  have hprev := st318_p293
  have hstep := st318_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p295 : ((8959737605671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT318 (i+1))
      = (∑ i ∈ Finset.range 294, stT318 (i+1)) + stT318 295 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 294
    simpa using h
  have hprev := st318_p294
  have hstep := st318_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p296 : ((9501922805689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT318 (i+1))
      = (∑ i ∈ Finset.range 295, stT318 (i+1)) + stT318 296 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 295
    simpa using h
  have hprev := st318_p295
  have hstep := st318_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p297 : ((9577025598629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT318 (i+1))
      = (∑ i ∈ Finset.range 296, stT318 (i+1)) + stT318 297 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 296
    simpa using h
  have hprev := st318_p296
  have hstep := st318_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p298 : ((4554751895767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT318 (i+1))
      = (∑ i ∈ Finset.range 297, stT318 (i+1)) + stT318 298 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 297
    simpa using h
  have hprev := st318_p297
  have hstep := st318_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p299 : ((8584632615629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT318 (i+1))
      = (∑ i ∈ Finset.range 298, stT318 (i+1)) + stT318 299 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 298
    simpa using h
  have hprev := st318_p298
  have hstep := st318_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p300 : ((4270515245379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT318 (i+1))
      = (∑ i ∈ Finset.range 299, stT318 (i+1)) + stT318 300 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 299
    simpa using h
  have hprev := st318_p299
  have hstep := st318_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p301 : ((2255135935377/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT318 (i+1))
      = (∑ i ∈ Finset.range 300, stT318 (i+1)) + stT318 301 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 300
    simpa using h
  have hprev := st318_p300
  have hstep := st318_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p302 : ((9534384754543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT318 (i+1))
      = (∑ i ∈ Finset.range 301, stT318 (i+1)) + stT318 302 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 301
    simpa using h
  have hprev := st318_p301
  have hstep := st318_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p303 : ((1912935803863/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT318 (i+1))
      = (∑ i ∈ Finset.range 302, stT318 (i+1)) + stT318 303 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 302
    simpa using h
  have hprev := st318_p302
  have hstep := st318_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p304 : ((363343379627/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT318 (i+1))
      = (∑ i ∈ Finset.range 303, stT318 (i+1)) + stT318 304 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 303
    simpa using h
  have hprev := st318_p303
  have hstep := st318_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p305 : ((171452229161/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT318 (i+1))
      = (∑ i ∈ Finset.range 304, stT318 (i+1)) + stT318 305 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 304
    simpa using h
  have hprev := st318_p304
  have hstep := st318_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p306 : ((853746567829/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT318 (i+1))
      = (∑ i ∈ Finset.range 305, stT318 (i+1)) + stT318 306 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 305
    simpa using h
  have hprev := st318_p305
  have hstep := st318_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p307 : ((180203022261/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT318 (i+1))
      = (∑ i ∈ Finset.range 306, stT318 (i+1)) + stT318 307 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 306
    simpa using h
  have hprev := st318_p306
  have hstep := st318_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p308 : ((119072026173/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT318 (i+1))
      = (∑ i ∈ Finset.range 307, stT318 (i+1)) + stT318 308 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 307
    simpa using h
  have hprev := st318_p307
  have hstep := st318_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p309 : ((23957054739/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT318 (i+1))
      = (∑ i ∈ Finset.range 308, stT318 (i+1)) + stT318 309 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 308
    simpa using h
  have hprev := st318_p308
  have hstep := st318_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p310 : ((2282133804513/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT318 (i+1))
      = (∑ i ∈ Finset.range 309, stT318 (i+1)) + stT318 310 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 309
    simpa using h
  have hprev := st318_p309
  have hstep := st318_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p311 : ((430096907709/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT318 (i+1))
      = (∑ i ∈ Finset.range 310, stT318 (i+1)) + stT318 311 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 310
    simpa using h
  have hprev := st318_p310
  have hstep := st318_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p312 : ((8506279345767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT318 (i+1))
      = (∑ i ∈ Finset.range 311, stT318 (i+1)) + stT318 312 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 311
    simpa using h
  have hprev := st318_p311
  have hstep := st318_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p313 : ((1786018888113/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT318 (i+1))
      = (∑ i ∈ Finset.range 312, stT318 (i+1)) + stT318 313 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 312
    simpa using h
  have hprev := st318_p312
  have hstep := st318_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p314 : ((1894113296721/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT318 (i+1))
      = (∑ i ∈ Finset.range 313, stT318 (i+1)) + stT318 314 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 313
    simpa using h
  have hprev := st318_p313
  have hstep := st318_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p315 : ((9619803213489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT318 (i+1))
      = (∑ i ∈ Finset.range 314, stT318 (i+1)) + stT318 315 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 314
    simpa using h
  have hprev := st318_p314
  have hstep := st318_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p316 : ((1848105972141/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT318 (i+1))
      = (∑ i ∈ Finset.range 315, stT318 (i+1)) + stT318 316 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 315
    simpa using h
  have hprev := st318_p315
  have hstep := st318_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p317 : ((69498142477/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT318 (i+1))
      = (∑ i ∈ Finset.range 316, stT318 (i+1)) + stT318 317 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 316
    simpa using h
  have hprev := st318_p316
  have hstep := st318_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p318 : ((211778577289/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT318 (i+1))
      = (∑ i ∈ Finset.range 317, stT318 (i+1)) + stT318 318 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 317
    simpa using h
  have hprev := st318_p317
  have hstep := st318_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p319 : ((2197143325267/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT318 (i+1))
      = (∑ i ∈ Finset.range 318, stT318 (i+1)) + stT318 319 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 318
    simpa using h
  have hprev := st318_p318
  have hstep := st318_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p320 : ((2336830942117/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT318 (i+1))
      = (∑ i ∈ Finset.range 319, stT318 (i+1)) + stT318 320 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 319
    simpa using h
  have hprev := st318_p319
  have hstep := st318_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p321 : ((1204945224091/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT318 (i+1))
      = (∑ i ∈ Finset.range 320, stT318 (i+1)) + stT318 321 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 320
    simpa using h
  have hprev := st318_p320
  have hstep := st318_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p322 : ((146924716779/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT318 (i+1))
      = (∑ i ∈ Finset.range 321, stT318 (i+1)) + stT318 322 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 321
    simpa using h
  have hprev := st318_p321
  have hstep := st318_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p323 : ((8852696588511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT318 (i+1))
      = (∑ i ∈ Finset.range 322, stT318 (i+1)) + stT318 323 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 322
    simpa using h
  have hprev := st318_p322
  have hstep := st318_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p324 : ((8480255735003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT318 (i+1))
      = (∑ i ∈ Finset.range 323, stT318 (i+1)) + stT318 324 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 323
    simpa using h
  have hprev := st318_p323
  have hstep := st318_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p325 : ((8614931902703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT318 (i+1))
      = (∑ i ∈ Finset.range 324, stT318 (i+1)) + stT318 325 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 324
    simpa using h
  have hprev := st318_p324
  have hstep := st318_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p326 : ((365417286431/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT318 (i+1))
      = (∑ i ∈ Finset.range 325, stT318 (i+1)) + stT318 326 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 325
    simpa using h
  have hprev := st318_p325
  have hstep := st318_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p327 : ((4791842685179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT318 (i+1))
      = (∑ i ∈ Finset.range 326, stT318 (i+1)) + stT318 327 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 326
    simpa using h
  have hprev := st318_p326
  have hstep := st318_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p328 : ((4784722055611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT318 (i+1))
      = (∑ i ∈ Finset.range 327, stT318 (i+1)) + stT318 328 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 327
    simpa using h
  have hprev := st318_p327
  have hstep := st318_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p329 : ((71151178633/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT318 (i+1))
      = (∑ i ∈ Finset.range 328, stT318 (i+1)) + stT318 329 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 328
    simpa using h
  have hprev := st318_p328
  have hstep := st318_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p330 : ((2099056799/2441406250 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT318 (i+1))
      = (∑ i ∈ Finset.range 329, stT318 (i+1)) + stT318 330 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 329
    simpa using h
  have hprev := st318_p329
  have hstep := st318_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p331 : ((2119352092501/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT318 (i+1))
      = (∑ i ∈ Finset.range 330, stT318 (i+1)) + stT318 331 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 330
    simpa using h
  have hprev := st318_p330
  have hstep := st318_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p332 : ((4423440077707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT318 (i+1))
      = (∑ i ∈ Finset.range 331, stT318 (i+1)) + stT318 332 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 331
    simpa using h
  have hprev := st318_p331
  have hstep := st318_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p333 : ((4695297879329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT318 (i+1))
      = (∑ i ∈ Finset.range 332, stT318 (i+1)) + stT318 333 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 332
    simpa using h
  have hprev := st318_p332
  have hstep := st318_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p334 : ((1206188366351/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT318 (i+1))
      = (∑ i ∈ Finset.range 333, stT318 (i+1)) + stT318 334 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 333
    simpa using h
  have hprev := st318_p333
  have hstep := st318_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p335 : ((470401577543/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT318 (i+1))
      = (∑ i ∈ Finset.range 334, stT318 (i+1)) + stT318 335 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 334
    simpa using h
  have hprev := st318_p334
  have hstep := st318_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p336 : ((443493334181/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT318 (i+1))
      = (∑ i ∈ Finset.range 335, stT318 (i+1)) + stT318 336 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 335
    simpa using h
  have hprev := st318_p335
  have hstep := st318_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p337 : ((1696491428741/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT318 (i+1))
      = (∑ i ∈ Finset.range 336, stT318 (i+1)) + stT318 337 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 336
    simpa using h
  have hprev := st318_p336
  have hstep := st318_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p338 : ((8564308517001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT318 (i+1))
      = (∑ i ∈ Finset.range 337, stT318 (i+1)) + stT318 338 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 337
    simpa using h
  have hprev := st318_p337
  have hstep := st318_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p339 : ((2261489978469/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT318 (i+1))
      = (∑ i ∈ Finset.range 338, stT318 (i+1)) + stT318 339 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 338
    simpa using h
  have hprev := st318_p338
  have hstep := st318_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p340 : ((1191587322941/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT318 (i+1))
      = (∑ i ∈ Finset.range 339, stT318 (i+1)) + stT318 340 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 339
    simpa using h
  have hprev := st318_p339
  have hstep := st318_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p341 : ((1203725717891/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT318 (i+1))
      = (∑ i ∈ Finset.range 340, stT318 (i+1)) + stT318 341 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 340
    simpa using h
  have hprev := st318_p340
  have hstep := st318_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p342 : ((4630422732107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT318 (i+1))
      = (∑ i ∈ Finset.range 341, stT318 (i+1)) + stT318 342 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 341
    simpa using h
  have hprev := st318_p341
  have hstep := st318_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p343 : ((2181003688841/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT318 (i+1))
      = (∑ i ∈ Finset.range 342, stT318 (i+1)) + stT318 343 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 342
    simpa using h
  have hprev := st318_p342
  have hstep := st318_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p344 : ((422417387523/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT318 (i+1))
      = (∑ i ∈ Finset.range 343, stT318 (i+1)) + stT318 344 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 343
    simpa using h
  have hprev := st318_p343
  have hstep := st318_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p345 : ((8651249013073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT318 (i+1))
      = (∑ i ∈ Finset.range 344, stT318 (i+1)) + stT318 345 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 344
    simpa using h
  have hprev := st318_p344
  have hstep := st318_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p346 : ((143284205077/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT318 (i+1))
      = (∑ i ∈ Finset.range 345, stT318 (i+1)) + stT318 346 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 345
    simpa using h
  have hprev := st318_p345
  have hstep := st318_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p347 : ((1199529528149/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT318 (i+1))
      = (∑ i ∈ Finset.range 346, stT318 (i+1)) + stT318 347 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 346
    simpa using h
  have hprev := st318_p346
  have hstep := st318_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p348 : ((1199644914203/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT318 (i+1))
      = (∑ i ∈ Finset.range 347, stT318 (i+1)) + stT318 348 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 347
    simpa using h
  have hprev := st318_p347
  have hstep := st318_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p349 : ((1146783885983/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT318 (i+1))
      = (∑ i ∈ Finset.range 348, stT318 (i+1)) + stT318 349 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 348
    simpa using h
  have hprev := st318_p348
  have hstep := st318_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p350 : ((2164069419279/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT318 (i+1))
      = (∑ i ∈ Finset.range 349, stT318 (i+1)) + stT318 350 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 349
    simpa using h
  have hprev := st318_p349
  have hstep := st318_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p351 : ((1688323963919/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT318 (i+1))
      = (∑ i ∈ Finset.range 350, stT318 (i+1)) + stT318 351 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 350
    simpa using h
  have hprev := st318_p350
  have hstep := st318_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p352 : ((347713567237/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT318 (i+1))
      = (∑ i ∈ Finset.range 351, stT318 (i+1)) + stT318 352 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 351
    simpa using h
  have hprev := st318_p351
  have hstep := st318_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p353 : ((9216645888349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT318 (i+1))
      = (∑ i ∈ Finset.range 352, stT318 (i+1)) + stT318 353 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 352
    simpa using h
  have hprev := st318_p352
  have hstep := st318_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p354 : ((9615527351903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT318 (i+1))
      = (∑ i ∈ Finset.range 353, stT318 (i+1)) + stT318 354 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 353
    simpa using h
  have hprev := st318_p353
  have hstep := st318_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p355 : ((9589977287603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT318 (i+1))
      = (∑ i ∈ Finset.range 354, stT318 (i+1)) + stT318 355 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 354
    simpa using h
  have hprev := st318_p354
  have hstep := st318_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p356 : ((9161110576787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT318 (i+1))
      = (∑ i ∈ Finset.range 355, stT318 (i+1)) + stT318 356 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 355
    simpa using h
  have hprev := st318_p355
  have hstep := st318_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p357 : ((8650107650717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT318 (i+1))
      = (∑ i ∈ Finset.range 356, stT318 (i+1)) + stT318 357 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 356
    simpa using h
  have hprev := st318_p356
  have hstep := st318_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p358 : ((8435752782891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT318 (i+1))
      = (∑ i ∈ Finset.range 357, stT318 (i+1)) + stT318 358 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 357
    simpa using h
  have hprev := st318_p357
  have hstep := st318_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p359 : ((4337250765113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT318 (i+1))
      = (∑ i ∈ Finset.range 358, stT318 (i+1)) + stT318 359 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 358
    simpa using h
  have hprev := st318_p358
  have hstep := st318_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p360 : ((2297292463729/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT318 (i+1))
      = (∑ i ∈ Finset.range 359, stT318 (i+1)) + stT318 360 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 359
    simpa using h
  have hprev := st318_p359
  have hstep := st318_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p361 : ((4801574616973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT318 (i+1))
      = (∑ i ∈ Finset.range 360, stT318 (i+1)) + stT318 361 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 360
    simpa using h
  have hprev := st318_p360
  have hstep := st318_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p362 : ((4808301354991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT318 (i+1))
      = (∑ i ∈ Finset.range 361, stT318 (i+1)) + stT318 362 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 361
    simpa using h
  have hprev := st318_p361
  have hstep := st318_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p363 : ((4610849617647/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT318 (i+1))
      = (∑ i ∈ Finset.range 362, stT318 (i+1)) + stT318 363 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 362
    simpa using h
  have hprev := st318_p362
  have hstep := st318_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p364 : ((1087979040447/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT318 (i+1))
      = (∑ i ∈ Finset.range 363, stT318 (i+1)) + stT318 364 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 363
    simpa using h
  have hprev := st318_p363
  have hstep := st318_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p365 : ((1054176187671/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT318 (i+1))
      = (∑ i ∈ Finset.range 364, stT318 (i+1)) + stT318 365 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 364
    simpa using h
  have hprev := st318_p364
  have hstep := st318_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p366 : ((2150342946429/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT318 (i+1))
      = (∑ i ∈ Finset.range 365, stT318 (i+1)) + stT318 366 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 365
    simpa using h
  have hprev := st318_p365
  have hstep := st318_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p367 : ((2271717223829/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT318 (i+1))
      = (∑ i ∈ Finset.range 366, stT318 (i+1)) + stT318 367 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 366
    simpa using h
  have hprev := st318_p366
  have hstep := st318_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p368 : ((4773453719659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT318 (i+1))
      = (∑ i ∈ Finset.range 367, stT318 (i+1)) + stT318 368 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 367
    simpa using h
  have hprev := st318_p367
  have hstep := st318_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p369 : ((2358315343/2441406250 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT318 (i+1))
      = (∑ i ∈ Finset.range 368, stT318 (i+1)) + stT318 369 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 368
    simpa using h
  have hprev := st318_p368
  have hstep := st318_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p370 : ((2337054512371/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT318 (i+1))
      = (∑ i ∈ Finset.range 369, stT318 (i+1)) + stT318 370 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 369
    simpa using h
  have hprev := st318_p369
  have hstep := st318_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p371 : ((4415136747117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT318 (i+1))
      = (∑ i ∈ Finset.range 370, stT318 (i+1)) + stT318 371 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 370
    simpa using h
  have hprev := st318_p370
  have hstep := st318_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p372 : ((4231855481117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT318 (i+1))
      = (∑ i ∈ Finset.range 371, stT318 (i+1)) + stT318 372 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 371
    simpa using h
  have hprev := st318_p371
  have hstep := st318_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p373 : ((4249574689387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT318 (i+1))
      = (∑ i ∈ Finset.range 372, stT318 (i+1)) + stT318 373 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 372
    simpa using h
  have hprev := st318_p372
  have hstep := st318_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p374 : ((8910486399317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT318 (i+1))
      = (∑ i ∈ Finset.range 373, stT318 (i+1)) + stT318 374 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 373
    simpa using h
  have hprev := st318_p373
  have hstep := st318_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p375 : ((588544237277/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT318 (i+1))
      = (∑ i ∈ Finset.range 374, stT318 (i+1)) + stT318 375 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 374
    simpa using h
  have hprev := st318_p374
  have hstep := st318_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p376 : ((2418850335223/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT318 (i+1))
      = (∑ i ∈ Finset.range 375, stT318 (i+1)) + stT318 376 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 375
    simpa using h
  have hprev := st318_p375
  have hstep := st318_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p377 : ((594613805633/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT318 (i+1))
      = (∑ i ∈ Finset.range 376, stT318 (i+1)) + stT318 377 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 376
    simpa using h
  have hprev := st318_p376
  have hstep := st318_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p378 : ((2260482481607/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT318 (i+1))
      = (∑ i ∈ Finset.range 377, stT318 (i+1)) + stT318 378 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 377
    simpa using h
  have hprev := st318_p377
  have hstep := st318_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p379 : ((4287571313293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT318 (i+1))
      = (∑ i ∈ Finset.range 378, stT318 (i+1)) + stT318 379 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 378
    simpa using h
  have hprev := st318_p378
  have hstep := st318_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p380 : ((4211237375313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT318 (i+1))
      = (∑ i ∈ Finset.range 379, stT318 (i+1)) + stT318 380 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 379
    simpa using h
  have hprev := st318_p379
  have hstep := st318_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p381 : ((542689436701/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT318 (i+1))
      = (∑ i ∈ Finset.range 380, stT318 (i+1)) + stT318 381 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 380
    simpa using h
  have hprev := st318_p380
  have hstep := st318_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p382 : ((71750464043/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT318 (i+1))
      = (∑ i ∈ Finset.range 381, stT318 (i+1)) + stT318 382 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 381
    simpa using h
  have hprev := st318_p381
  have hstep := st318_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p383 : ((74980918187/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT318 (i+1))
      = (∑ i ∈ Finset.range 382, stT318 (i+1)) + stT318 383 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 382
    simpa using h
  have hprev := st318_p382
  have hstep := st318_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p384 : ((4827726353873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT318 (i+1))
      = (∑ i ∈ Finset.range 383, stT318 (i+1)) + stT318 384 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 383
    simpa using h
  have hprev := st318_p383
  have hstep := st318_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p385 : ((4660969273449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT318 (i+1))
      = (∑ i ∈ Finset.range 384, stT318 (i+1)) + stT318 385 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 384
    simpa using h
  have hprev := st318_p384
  have hstep := st318_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p386 : ((8813171938269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT318 (i+1))
      = (∑ i ∈ Finset.range 385, stT318 (i+1)) + stT318 386 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 385
    simpa using h
  have hprev := st318_p385
  have hstep := st318_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p387 : ((8455377455013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT318 (i+1))
      = (∑ i ∈ Finset.range 386, stT318 (i+1)) + stT318 387 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 386
    simpa using h
  have hprev := st318_p386
  have hstep := st318_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p388 : ((8475618377523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT318 (i+1))
      = (∑ i ∈ Finset.range 387, stT318 (i+1)) + stT318 388 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 387
    simpa using h
  have hprev := st318_p387
  have hstep := st318_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p389 : ((8859316409943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT318 (i+1))
      = (∑ i ∈ Finset.range 388, stT318 (i+1)) + stT318 389 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 388
    simpa using h
  have hprev := st318_p388
  have hstep := st318_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p390 : ((1170361344929/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT318 (i+1))
      = (∑ i ∈ Finset.range 389, stT318 (i+1)) + stT318 390 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 389
    simpa using h
  have hprev := st318_p389
  have hstep := st318_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p391 : ((4834912991539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT318 (i+1))
      = (∑ i ∈ Finset.range 390, stT318 (i+1)) + stT318 391 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 390
    simpa using h
  have hprev := st318_p390
  have hstep := st318_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p392 : ((14983327877/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT318 (i+1))
      = (∑ i ∈ Finset.range 391, stT318 (i+1)) + stT318 392 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 391
    simpa using h
  have hprev := st318_p391
  have hstep := st318_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p393 : ((2293283615791/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT318 (i+1))
      = (∑ i ∈ Finset.range 392, stT318 (i+1)) + stT318 393 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 392
    simpa using h
  have hprev := st318_p392
  have hstep := st318_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p394 : ((8680096939921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT318 (i+1))
      = (∑ i ∈ Finset.range 393, stT318 (i+1)) + stT318 394 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 393
    simpa using h
  have hprev := st318_p393
  have hstep := st318_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p395 : ((2103489156189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT318 (i+1))
      = (∑ i ∈ Finset.range 394, stT318 (i+1)) + stT318 395 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 394
    simpa using h
  have hprev := st318_p394
  have hstep := st318_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p396 : ((4268342544171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT318 (i+1))
      = (∑ i ∈ Finset.range 395, stT318 (i+1)) + stT318 396 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 395
    simpa using h
  have hprev := st318_p395
  have hstep := st318_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p397 : ((4485843442851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT318 (i+1))
      = (∑ i ∈ Finset.range 396, stT318 (i+1)) + stT318 397 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 396
    simpa using h
  have hprev := st318_p396
  have hstep := st318_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p398 : ((2363409774481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT318 (i+1))
      = (∑ i ∈ Finset.range 397, stT318 (i+1)) + stT318 398 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 397
    simpa using h
  have hprev := st318_p397
  have hstep := st318_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p399 : ((302852977231/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT318 (i+1))
      = (∑ i ∈ Finset.range 398, stT318 (i+1)) + stT318 399 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 398
    simpa using h
  have hprev := st318_p398
  have hstep := st318_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p400 : ((4771448987299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT318 (i+1))
      = (∑ i ∈ Finset.range 399, stT318 (i+1)) + stT318 400 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 399
    simpa using h
  have hprev := st318_p399
  have hstep := st318_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p401 : ((1819776481639/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT318 (i+1))
      = (∑ i ∈ Finset.range 400, stT318 (i+1)) + stT318 401 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 400
    simpa using h
  have hprev := st318_p400
  have hstep := st318_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p402 : ((344993748439/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT318 (i+1))
      = (∑ i ∈ Finset.range 401, stT318 (i+1)) + stT318 402 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 401
    simpa using h
  have hprev := st318_p401
  have hstep := st318_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p403 : ((8401744536927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT318 (i+1))
      = (∑ i ∈ Finset.range 402, stT318 (i+1)) + stT318 403 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 402
    simpa using h
  have hprev := st318_p402
  have hstep := st318_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p404 : ((1712001102049/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT318 (i+1))
      = (∑ i ∈ Finset.range 403, stT318 (i+1)) + stT318 404 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 403
    simpa using h
  have hprev := st318_p403
  have hstep := st318_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p405 : ((900502935253/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT318 (i+1))
      = (∑ i ∈ Finset.range 404, stT318 (i+1)) + stT318 405 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 404
    simpa using h
  have hprev := st318_p404
  have hstep := st318_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p406 : ((4737770506413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT318 (i+1))
      = (∑ i ∈ Finset.range 405, stT318 (i+1)) + stT318 406 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 405
    simpa using h
  have hprev := st318_p405
  have hstep := st318_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p407 : ((242445282819/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT318 (i+1))
      = (∑ i ∈ Finset.range 406, stT318 (i+1)) + stT318 407 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 406
    simpa using h
  have hprev := st318_p406
  have hstep := st318_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p408 : ((4772126362479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT318 (i+1))
      = (∑ i ∈ Finset.range 407, stT318 (i+1)) + stT318 408 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 407
    simpa using h
  have hprev := st318_p407
  have hstep := st318_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p409 : ((4552471365423/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT318 (i+1))
      = (∑ i ∈ Finset.range 408, stT318 (i+1)) + stT318 409 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 408
    simpa using h
  have hprev := st318_p408
  have hstep := st318_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p410 : ((2158253062739/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT318 (i+1))
      = (∑ i ∈ Finset.range 409, stT318 (i+1)) + stT318 410 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 409
    simpa using h
  have hprev := st318_p409
  have hstep := st318_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p411 : ((419897142619/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT318 (i+1))
      = (∑ i ∈ Finset.range 410, stT318 (i+1)) + stT318 411 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 410
    simpa using h
  have hprev := st318_p410
  have hstep := st318_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p412 : ((2133054975893/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT318 (i+1))
      = (∑ i ∈ Finset.range 411, stT318 (i+1)) + stT318 412 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 411
    simpa using h
  have hprev := st318_p411
  have hstep := st318_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p413 : ((1791655124691/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT318 (i+1))
      = (∑ i ∈ Finset.range 412, stT318 (i+1)) + stT318 413 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 412
    simpa using h
  have hprev := st318_p412
  have hstep := st318_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p414 : ((94349872319/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT318 (i+1))
      = (∑ i ∈ Finset.range 413, stT318 (i+1)) + stT318 414 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 413
    simpa using h
  have hprev := st318_p413
  have hstep := st318_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p415 : ((484748772123/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT318 (i+1))
      = (∑ i ∈ Finset.range 414, stT318 (i+1)) + stT318 415 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 414
    simpa using h
  have hprev := st318_p414
  have hstep := st318_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p416 : ((2398535058559/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT318 (i+1))
      = (∑ i ∈ Finset.range 415, stT318 (i+1)) + stT318 416 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 415
    simpa using h
  have hprev := st318_p415
  have hstep := st318_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p417 : ((9189987858633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT318 (i+1))
      = (∑ i ∈ Finset.range 416, stT318 (i+1)) + stT318 417 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 416
    simpa using h
  have hprev := st318_p416
  have hstep := st318_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p418 : ((1741436486653/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT318 (i+1))
      = (∑ i ∈ Finset.range 417, stT318 (i+1)) + stT318 418 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 417
    simpa using h
  have hprev := st318_p417
  have hstep := st318_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p419 : ((8411675288849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT318 (i+1))
      = (∑ i ∈ Finset.range 418, stT318 (i+1)) + stT318 419 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 418
    simpa using h
  have hprev := st318_p418
  have hstep := st318_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p420 : ((8464489045049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT318 (i+1))
      = (∑ i ∈ Finset.range 419, stT318 (i+1)) + stT318 420 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 419
    simpa using h
  have hprev := st318_p419
  have hstep := st318_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p421 : ((8835307433769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT318 (i+1))
      = (∑ i ∈ Finset.range 420, stT318 (i+1)) + stT318 421 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 420
    simpa using h
  have hprev := st318_p420
  have hstep := st318_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p422 : ((9321479747553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT318 (i+1))
      = (∑ i ∈ Finset.range 421, stT318 (i+1)) + stT318 422 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 421
    simpa using h
  have hprev := st318_p421
  have hstep := st318_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p423 : ((9659802454401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT318 (i+1))
      = (∑ i ∈ Finset.range 422, stT318 (i+1)) + stT318 423 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 422
    simpa using h
  have hprev := st318_p422
  have hstep := st318_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p424 : ((9668891730073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT318 (i+1))
      = (∑ i ∈ Finset.range 423, stT318 (i+1)) + stT318 424 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 423
    simpa using h
  have hprev := st318_p423
  have hstep := st318_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p425 : ((9345256542393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT318 (i+1))
      = (∑ i ∈ Finset.range 424, stT318 (i+1)) + stT318 425 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 424
    simpa using h
  have hprev := st318_p424
  have hstep := st318_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p426 : ((8862805923861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT318 (i+1))
      = (∑ i ∈ Finset.range 425, stT318 (i+1)) + stT318 426 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 425
    simpa using h
  have hprev := st318_p425
  have hstep := st318_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p427 : ((8478232284873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT318 (i+1))
      = (∑ i ∈ Finset.range 426, stT318 (i+1)) + stT318 427 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 426
    simpa using h
  have hprev := st318_p426
  have hstep := st318_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p428 : ((2098567651551/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT318 (i+1))
      = (∑ i ∈ Finset.range 427, stT318 (i+1)) + stT318 428 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 427
    simpa using h
  have hprev := st318_p427
  have hstep := st318_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p429 : ((1081726021607/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT318 (i+1))
      = (∑ i ∈ Finset.range 428, stT318 (i+1)) + stT318 429 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 428
    simpa using h
  have hprev := st318_p428
  have hstep := st318_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p430 : ((1139931666523/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT318 (i+1))
      = (∑ i ∈ Finset.range 429, stT318 (i+1)) + stT318 430 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 429
    simpa using h
  have hprev := st318_p429
  have hstep := st318_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p431 : ((9547560177143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT318 (i+1))
      = (∑ i ∈ Finset.range 430, stT318 (i+1)) + stT318 431 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 430
    simpa using h
  have hprev := st318_p430
  have hstep := st318_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p432 : ((9716060736893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT318 (i+1))
      = (∑ i ∈ Finset.range 431, stT318 (i+1)) + stT318 432 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 431
    simpa using h
  have hprev := st318_p431
  have hstep := st318_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p433 : ((9538936090853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT318 (i+1))
      = (∑ i ∈ Finset.range 432, stT318 (i+1)) + stT318 433 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 432
    simpa using h
  have hprev := st318_p432
  have hstep := st318_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p434 : ((9108740471477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT318 (i+1))
      = (∑ i ∈ Finset.range 433, stT318 (i+1)) + stT318 434 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 433
    simpa using h
  have hprev := st318_p433
  have hstep := st318_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p435 : ((1729371395593/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT318 (i+1))
      = (∑ i ∈ Finset.range 434, stT318 (i+1)) + stT318 435 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 434
    simpa using h
  have hprev := st318_p434
  have hstep := st318_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p436 : ((1677787568653/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT318 (i+1))
      = (∑ i ∈ Finset.range 435, stT318 (i+1)) + stT318 436 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 435
    simpa using h
  have hprev := st318_p435
  have hstep := st318_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p437 : ((8465059428221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT318 (i+1))
      = (∑ i ∈ Finset.range 436, stT318 (i+1)) + stT318 437 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 436
    simpa using h
  have hprev := st318_p436
  have hstep := st318_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p438 : ((8835344487321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT318 (i+1))
      = (∑ i ∈ Finset.range 437, stT318 (i+1)) + stT318 438 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 437
    simpa using h
  have hprev := st318_p437
  have hstep := st318_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p439 : ((9312165032517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT318 (i+1))
      = (∑ i ∈ Finset.range 438, stT318 (i+1)) + stT318 439 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 438
    simpa using h
  have hprev := st318_p438
  have hstep := st318_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p440 : ((2414026964127/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT318 (i+1))
      = (∑ i ∈ Finset.range 439, stT318 (i+1)) + stT318 440 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 439
    simpa using h
  have hprev := st318_p439
  have hstep := st318_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p441 : ((4848045098739/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT318 (i+1))
      = (∑ i ∈ Finset.range 440, stT318 (i+1)) + stT318 441 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 440
    simpa using h
  have hprev := st318_p440
  have hstep := st318_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p442 : ((941347252429/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT318 (i+1))
      = (∑ i ∈ Finset.range 441, stT318 (i+1)) + stT318 442 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 441
    simpa using h
  have hprev := st318_p441
  have hstep := st318_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p443 : ((111866931701/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT318 (i+1))
      = (∑ i ∈ Finset.range 442, stT318 (i+1)) + stT318 443 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 442
    simpa using h
  have hprev := st318_p442
  have hstep := st318_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p444 : ((853304909149/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT318 (i+1))
      = (∑ i ∈ Finset.range 443, stT318 (i+1)) + stT318 444 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 443
    simpa using h
  have hprev := st318_p443
  have hstep := st318_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p445 : ((2092123020343/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT318 (i+1))
      = (∑ i ∈ Finset.range 444, stT318 (i+1)) + stT318 445 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 444
    simpa using h
  have hprev := st318_p444
  have hstep := st318_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p446 : ((33339799697/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT318 (i+1))
      = (∑ i ∈ Finset.range 445, stT318 (i+1)) + stT318 446 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 445
    simpa using h
  have hprev := st318_p445
  have hstep := st318_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p447 : ((2237551340669/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT318 (i+1))
      = (∑ i ∈ Finset.range 446, stT318 (i+1)) + stT318 447 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 446
    simpa using h
  have hprev := st318_p446
  have hstep := st318_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p448 : ((4706045772163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT318 (i+1))
      = (∑ i ∈ Finset.range 447, stT318 (i+1)) + stT318 448 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 447
    simpa using h
  have hprev := st318_p447
  have hstep := st318_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p449 : ((4848889241883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT318 (i+1))
      = (∑ i ∈ Finset.range 448, stT318 (i+1)) + stT318 449 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 448
    simpa using h
  have hprev := st318_p448
  have hstep := st318_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p450 : ((9670824017271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT318 (i+1))
      = (∑ i ∈ Finset.range 449, stT318 (i+1)) + stT318 450 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 449
    simpa using h
  have hprev := st318_p449
  have hstep := st318_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p451 : ((1869070264127/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT318 (i+1))
      = (∑ i ∈ Finset.range 450, stT318 (i+1)) + stT318 451 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 450
    simpa using h
  have hprev := st318_p450
  have hstep := st318_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p452 : ((1775491943177/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT318 (i+1))
      = (∑ i ∈ Finset.range 451, stT318 (i+1)) + stT318 452 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 451
    simpa using h
  have hprev := st318_p451
  have hstep := st318_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p453 : ((8489449983173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT318 (i+1))
      = (∑ i ∈ Finset.range 452, stT318 (i+1)) + stT318 453 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 452
    simpa using h
  have hprev := st318_p452
  have hstep := st318_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p454 : ((8364079932377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT318 (i+1))
      = (∑ i ∈ Finset.range 453, stT318 (i+1)) + stT318 454 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 453
    simpa using h
  have hprev := st318_p453
  have hstep := st318_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p455 : ((2139800875067/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT318 (i+1))
      = (∑ i ∈ Finset.range 454, stT318 (i+1)) + stT318 455 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 454
    simpa using h
  have hprev := st318_p454
  have hstep := st318_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p456 : ((70173356673/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT318 (i+1))
      = (∑ i ∈ Finset.range 455, stT318 (i+1)) + stT318 456 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 455
    simpa using h
  have hprev := st318_p455
  have hstep := st318_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p457 : ((2358748887141/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT318 (i+1))
      = (∑ i ∈ Finset.range 456, stT318 (i+1)) + stT318 457 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 456
    simpa using h
  have hprev := st318_p456
  have hstep := st318_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p458 : ((606710181907/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT318 (i+1))
      = (∑ i ∈ Finset.range 457, stT318 (i+1)) + stT318 458 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 457
    simpa using h
  have hprev := st318_p457
  have hstep := st318_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p459 : ((1209264790631/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT318 (i+1))
      = (∑ i ∈ Finset.range 458, stT318 (i+1)) + stT318 459 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 458
    simpa using h
  have hprev := st318_p458
  have hstep := st318_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p460 : ((9351774779751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT318 (i+1))
      = (∑ i ∈ Finset.range 459, stT318 (i+1)) + stT318 460 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 459
    simpa using h
  have hprev := st318_p459
  have hstep := st318_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p461 : ((8889165983037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT318 (i+1))
      = (∑ i ∈ Finset.range 460, stT318 (i+1)) + stT318 461 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 460
    simpa using h
  have hprev := st318_p460
  have hstep := st318_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p462 : ((1699588256673/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT318 (i+1))
      = (∑ i ∈ Finset.range 461, stT318 (i+1)) + stT318 462 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 461
    simpa using h
  have hprev := st318_p461
  have hstep := st318_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p463 : ((1671119399649/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT318 (i+1))
      = (∑ i ∈ Finset.range 462, stT318 (i+1)) + stT318 463 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 462
    simpa using h
  have hprev := st318_p462
  have hstep := st318_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p464 : ((8525544316809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT318 (i+1))
      = (∑ i ∈ Finset.range 463, stT318 (i+1)) + stT318 464 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 463
    simpa using h
  have hprev := st318_p463
  have hstep := st318_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p465 : ((8929933591307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT318 (i+1))
      = (∑ i ∈ Finset.range 464, stT318 (i+1)) + stT318 465 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 464
    simpa using h
  have hprev := st318_p464
  have hstep := st318_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p466 : ((9386304727277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT318 (i+1))
      = (∑ i ∈ Finset.range 465, stT318 (i+1)) + stT318 466 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 465
    simpa using h
  have hprev := st318_p465
  have hstep := st318_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p467 : ((1938087441121/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT318 (i+1))
      = (∑ i ∈ Finset.range 466, stT318 (i+1)) + stT318 467 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 466
    simpa using h
  have hprev := st318_p466
  have hstep := st318_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p468 : ((1941505225171/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT318 (i+1))
      = (∑ i ∈ Finset.range 467, stT318 (i+1)) + stT318 468 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 467
    simpa using h
  have hprev := st318_p467
  have hstep := st318_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p469 : ((9431093313881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT318 (i+1))
      = (∑ i ∈ Finset.range 468, stT318 (i+1)) + stT318 469 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 468
    simpa using h
  have hprev := st318_p468
  have hstep := st318_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p470 : ((8984326288059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT318 (i+1))
      = (∑ i ∈ Finset.range 469, stT318 (i+1)) + stT318 470 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 469
    simpa using h
  have hprev := st318_p469
  have hstep := st318_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p471 : ((8564321130867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT318 (i+1))
      = (∑ i ∈ Finset.range 470, stT318 (i+1)) + stT318 471 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 470
    simpa using h
  have hprev := st318_p470
  have hstep := st318_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p472 : ((8354886868851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT318 (i+1))
      = (∑ i ∈ Finset.range 471, stT318 (i+1)) + stT318 472 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 471
    simpa using h
  have hprev := st318_p471
  have hstep := st318_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p473 : ((8446525928451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT318 (i+1))
      = (∑ i ∈ Finset.range 472, stT318 (i+1)) + stT318 473 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 472
    simpa using h
  have hprev := st318_p472
  have hstep := st318_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p474 : ((1099780856127/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT318 (i+1))
      = (∑ i ∈ Finset.range 473, stT318 (i+1)) + stT318 474 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 473
    simpa using h
  have hprev := st318_p473
  have hstep := st318_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p475 : ((9256848892347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT318 (i+1))
      = (∑ i ∈ Finset.range 474, stT318 (i+1)) + stT318 475 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 474
    simpa using h
  have hprev := st318_p474
  have hstep := st318_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p476 : ((2406076019301/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT318 (i+1))
      = (∑ i ∈ Finset.range 475, stT318 (i+1)) + stT318 476 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 475
    simpa using h
  have hprev := st318_p475
  have hstep := st318_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p477 : ((2435816377373/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT318 (i+1))
      = (∑ i ∈ Finset.range 476, stT318 (i+1)) + stT318 477 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 476
    simpa using h
  have hprev := st318_p476
  have hstep := st318_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p478 : ((2390954651393/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT318 (i+1))
      = (∑ i ∈ Finset.range 477, stT318 (i+1)) + stT318 478 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 477
    simpa using h
  have hprev := st318_p477
  have hstep := st318_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p479 : ((2290873789193/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT318 (i+1))
      = (∑ i ∈ Finset.range 478, stT318 (i+1)) + stT318 479 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 478
    simpa using h
  have hprev := st318_p478
  have hstep := st318_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p480 : ((435642292619/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT318 (i+1))
      = (∑ i ∈ Finset.range 479, stT318 (i+1)) + stT318 480 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 479
    simpa using h
  have hprev := st318_p479
  have hstep := st318_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p481 : ((8402342338873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT318 (i+1))
      = (∑ i ∈ Finset.range 480, stT318 (i+1)) + stT318 481 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 480
    simpa using h
  have hprev := st318_p480
  have hstep := st318_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p482 : ((8362029828921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT318 (i+1))
      = (∑ i ∈ Finset.range 481, stT318 (i+1)) + stT318 482 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 481
    simpa using h
  have hprev := st318_p481
  have hstep := st318_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p483 : ((4303865096833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT318 (i+1))
      = (∑ i ∈ Finset.range 482, stT318 (i+1)) + stT318 483 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 482
    simpa using h
  have hprev := st318_p482
  have hstep := st318_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p484 : ((4517911246423/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT318 (i+1))
      = (∑ i ∈ Finset.range 483, stT318 (i+1)) + stT318 484 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 483
    simpa using h
  have hprev := st318_p483
  have hstep := st318_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p485 : ((946768237047/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT318 (i+1))
      = (∑ i ∈ Finset.range 484, stT318 (i+1)) + stT318 485 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 484
    simpa using h
  have hprev := st318_p484
  have hstep := st318_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p486 : ((9724512611007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT318 (i+1))
      = (∑ i ∈ Finset.range 485, stT318 (i+1)) + stT318 486 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 485
    simpa using h
  have hprev := st318_p485
  have hstep := st318_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p487 : ((9701073737607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT318 (i+1))
      = (∑ i ∈ Finset.range 486, stT318 (i+1)) + stT318 487 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 486
    simpa using h
  have hprev := st318_p486
  have hstep := st318_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p488 : ((940803515571/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT318 (i+1))
      = (∑ i ∈ Finset.range 487, stT318 (i+1)) + stT318 488 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 487
    simpa using h
  have hprev := st318_p487
  have hstep := st318_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p489 : ((4483135838167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT318 (i+1))
      = (∑ i ∈ Finset.range 488, stT318 (i+1)) + stT318 489 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 488
    simpa using h
  have hprev := st318_p488
  have hstep := st318_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p490 : ((1069538397513/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT318 (i+1))
      = (∑ i ∈ Finset.range 489, stT318 (i+1)) + stT318 490 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 489
    simpa using h
  have hprev := st318_p489
  have hstep := st318_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p491 : ((2086096910249/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT318 (i+1))
      = (∑ i ∈ Finset.range 490, stT318 (i+1)) + stT318 491 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 490
    simpa using h
  have hprev := st318_p490
  have hstep := st318_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p492 : ((1051926390961/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT318 (i+1))
      = (∑ i ∈ Finset.range 491, stT318 (i+1)) + stT318 492 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 491
    simpa using h
  have hprev := st318_p491
  have hstep := st318_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p493 : ((8739688422589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT318 (i+1))
      = (∑ i ∈ Finset.range 492, stT318 (i+1)) + stT318 493 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 492
    simpa using h
  have hprev := st318_p492
  have hstep := st318_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p494 : ((9186196321883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT318 (i+1))
      = (∑ i ∈ Finset.range 493, stT318 (i+1)) + stT318 494 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 493
    simpa using h
  have hprev := st318_p493
  have hstep := st318_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p495 : ((9576067175477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT318 (i+1))
      = (∑ i ∈ Finset.range 494, stT318 (i+1)) + stT318 495 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 494
    simpa using h
  have hprev := st318_p494
  have hstep := st318_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p496 : ((2438584364957/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT318 (i+1))
      = (∑ i ∈ Finset.range 495, stT318 (i+1)) + stT318 496 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 495
    simpa using h
  have hprev := st318_p495
  have hstep := st318_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p497 : ((4825556961913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT318 (i+1))
      = (∑ i ∈ Finset.range 496, stT318 (i+1)) + stT318 497 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 496
    simpa using h
  have hprev := st318_p496
  have hstep := st318_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p498 : ((9308195636743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT318 (i+1))
      = (∑ i ∈ Finset.range 497, stT318 (i+1)) + stT318 498 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 497
    simpa using h
  have hprev := st318_p497
  have hstep := st318_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p499 : ((8861338085357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT318 (i+1))
      = (∑ i ∈ Finset.range 498, stT318 (i+1)) + stT318 499 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 498
    simpa using h
  have hprev := st318_p498
  have hstep := st318_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_p500 : ((1697200242773/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT318 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT318 (i+1))
      = (∑ i ∈ Finset.range 499, stT318 (i+1)) + stT318 500 := by
    have h := Finset.sum_range_succ (fun i => stT318 (i+1)) 499
    simpa using h
  have hprev := st318_p499
  have hstep := st318_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st318_s500 :
    |Real.sin (((318 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))
      - ((-543857/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -1283283/2000000) (δ := 401/25000000) (ψ := -195723/500000) 318 315
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 318`** (evaluated boundary). -/
theorem station_318_sign : 0 < hardyG ((((318:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 318 500 (by norm_num) (by norm_num)
    ((-195723/500000 : ℚ) : ℝ)
  have hchain := st318_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT318 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((318 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-195723/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st318_c500
  have hsinb := abs_le.mp st318_s500
  have hbdy_lo : ((15503467330689/404497000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((318 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-195723/500000 : ℚ) : ℝ))) / 2
          - ((((318:ℕ)):ℝ))
            * Real.sin (((318 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-195723/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((318:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((318:ℝ) * Real.log (500:ℝ) - ((-195723/500000 : ℚ) : ℝ))) / 2
        - ((318:ℝ)) * Real.sin ((318:ℝ) * Real.log (500:ℝ) - ((-195723/500000 : ℚ) : ℝ))
        ≥ ((34666853/200000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((318:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((34666853/200000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((34666853/200000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((34666853/200000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((318:ℕ)):ℝ))+1) * (((((318:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((18410235131/23437500000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1697200242773/2000000000000 : ℚ) : ℝ) + ((15503467330689/404497000000000 : ℚ) : ℝ)
      - ((18410235131/23437500000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-195723/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((318:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-195723/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((318:ℕ)):ℝ)))).re
      - Real.sin ((-195723/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((318:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((318:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((318:ℕ)):ℝ))
      = (((((318:ℕ)):ℝ)) * (Real.log ((((318:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((318:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_318
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
  have hθwin : |(((-195723/500000 : ℚ) : ℝ) + ((74:ℤ)) * (2*Real.pi)) - theta ((((318:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((318:ℕ)):ℝ)))
    (φ := ((-195723/500000 : ℚ) : ℝ) + ((74:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-195723/500000 : ℚ)) : ℝ) 74).1,
    (cos_sin_shift (((-195723/500000 : ℚ)) : ℝ) 74).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_318_sign
end AxiomAudit
