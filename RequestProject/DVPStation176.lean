import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 176` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT176 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((176 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((343219/500000 : ℚ) : ℝ))

theorem st176_c1 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((193377/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -343219/2000000) (δ := 1/1000000000) (ψ := 343219/500000) 176 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t1 : ((386729/500000 : ℚ) : ℝ) ≤ stT176 1 := by
  have hc : ((386729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((386729/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((386729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c2 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-174331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4817349/10000000) (δ := 4419/500000000) (ψ := 343219/500000) 176 19
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t2 : ((-77055195763/312500000000 : ℚ) : ℝ) ≤ stT176 2 := by
  have hc : ((-43589/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77055195763/312500000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-43589/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c3 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-512961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2636783/5000000) (δ := 2231/250000000) (ψ := 343219/500000) 176 31
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t3 : ((-2961870547533/10000000000000 : ℚ) : ℝ) ≤ stT176 3 := by
  have hc : ((-513011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2961870547533/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-513011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c4 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-34243/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1089287/2500000) (δ := 4491/500000000) (ψ := 343219/500000) 176 39
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t4 : ((-171265034253/2000000000000 : ℚ) : ℝ) ≤ stT176 4 := by
  have hc : ((-34253/200000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171265034253/2000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-34253/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c5 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((246451/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -26359/625000) (δ := 353/40000000) (ψ := 343219/500000) 176 45
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t5 : ((440842496479/1000000000000 : ℚ) : ℝ) ≤ stT176 5 := by
  have hc : ((492877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((440842496479/1000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((492877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c6 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((875677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12599/100000) (δ := 7/781250) (ψ := 343219/500000) 176 50
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t6 : ((1787365733107/5000000000000 : ℚ) : ℝ) ≤ stT176 6 := by
  have hc : ((875627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1787365733107/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((875627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c7 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-160437/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1250871/2000000) (δ := 8989/1000000000) (ψ := 343219/500000) 176 54
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t7 : ((-121286540263/400000000000 : ℚ) : ℝ) ≤ stT176 7 := by
  have hc : ((-160447/200000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121286540263/400000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-160447/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c8 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((80553/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2176317/10000000) (δ := 1797/200000000) (ψ := 343219/500000) 176 58
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t8 : ((1139102770671/5000000000000 : ℚ) : ℝ) ≤ stT176 8 := by
  have hc : ((322187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1139102770671/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((322187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c9 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-924599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1719237/2500000) (δ := 8939/1000000000) (ψ := 343219/500000) 176 61
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t9 : ((-1541081974883/5000000000000 : ℚ) : ℝ) ≤ stT176 9 := by
  have hc : ((-924649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1541081974883/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-924649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c10 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-383411/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3055839/5000000) (δ := 8861/1000000000) (ψ := 343219/500000) 176 64
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t10 : ((-151566403401/625000000000 : ℚ) : ℝ) ≤ stT176 10 := by
  have hc : ((-95859/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151566403401/625000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-95859/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c11 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((58277/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 231069/2500000) (δ := 441/50000000) (ψ := 343219/500000) 176 67
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t11 : ((1405618544583/5000000000000 : ℚ) : ℝ) ≤ stT176 11 := by
  have hc : ((466191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1405618544583/5000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((466191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c12 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-499853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3896683/5000000) (δ := 8997/1000000000) (ψ := 343219/500000) 176 69
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t12 : ((-22547247129/78125000000 : ℚ) : ℝ) ≤ stT176 12 := by
  have hc : ((-249939/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22547247129/78125000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-249939/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c13 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-73831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -513967/1250000) (δ := 4459/500000000) (ψ := 343219/500000) 176 72
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t13 : ((-204909027381/10000000000000 : ℚ) : ℝ) ≤ stT176 13 := by
  have hc : ((-73881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204909027381/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-73881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c14 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((19597/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2920143/10000000) (δ := 887/100000000) (ψ := 343219/500000) 176 74
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t14 : ((26184247917/250000000000 : ℚ) : ℝ) ≤ stT176 14 := by
  have hc : ((39189/100000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26184247917/250000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((39189/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c15 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-20879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3979193/10000000) (δ := 8947/1000000000) (ψ := 343219/500000) 176 76
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t15 : ((-54038447781/10000000000000 : ℚ) : ℝ) ≤ stT176 15 := by
  have hc : ((-20929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54038447781/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-20929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c16 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-470989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -349909/500000) (δ := 8841/1000000000) (ψ := 343219/500000) 176 78
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t16 : ((-588767735507/2500000000000 : ℚ) : ℝ) ≤ stT176 16 := by
  have hc : ((-235507/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-588767735507/2500000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-235507/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c17 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-667/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3968681/10000000) (δ := 8869/1000000000) (ψ := 343219/500000) 176 79
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t17 : ((-1622563833/400000000000 : ℚ) : ℝ) ≤ stT176 17 := by
  have hc : ((-669/40000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1622563833/400000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-669/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c18 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((3033/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -45951/200000) (δ := 223/25000000) (ψ := 343219/500000) 176 81
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t18 : ((14296516941/100000000000 : ℚ) : ℝ) ≤ stT176 18 := by
  have hc : ((12131/20000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14296516941/100000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((12131/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c19 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-169093/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1156811/2000000) (δ := 8813/1000000000) (ψ := 343219/500000) 176 82
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t19 : ((-387954735669/2500000000000 : ℚ) : ℝ) ≤ stT176 19 := by
  have hc : ((-338211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-387954735669/2500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-338211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c20 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((169413/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -153141/500000) (δ := 4499/500000000) (ψ := 343219/500000) 176 84
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t20 : ((94690729249/1250000000000 : ℚ) : ℝ) ≤ stT176 20 := by
  have hc : ((42347/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94690729249/1250000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((42347/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c21 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((23621/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 539381/2000000) (δ := 8891/1000000000) (ψ := 343219/500000) 176 85
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t21 : ((51539771093/500000000000 : ℚ) : ℝ) ≤ stT176 21 := by
  have hc : ((47237/100000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51539771093/500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((47237/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c22 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-493733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3728871/5000000) (δ := 8819/1000000000) (ψ := 343219/500000) 176 86
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t22 : ((-65793500379/312500000000 : ℚ) : ℝ) ≤ stT176 22 := by
  have hc : ((-246879/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65793500379/312500000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-246879/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c23 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-93919/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4399393/10000000) (δ := 897/100000000) (ψ := 343219/500000) 176 88
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t23 : ((-4897171547/125000000000 : ℚ) : ℝ) ≤ stT176 23 := by
  have hc : ((-11743/62500 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4897171547/125000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-11743/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c24 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((21281/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -345283/2500000) (δ := 8863/1000000000) (ψ := 343219/500000) 176 89
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t24 : ((173748392679/1000000000000 : ℚ) : ℝ) ≤ stT176 24 := by
  have hc : ((85119/100000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173748392679/1000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((85119/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c25 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((117463/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 174517/2000000) (δ := 553/62500000) (ψ := 343219/500000) 176 90
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t25 : ((469827/2500000 : ℚ) : ℝ) ≤ stT176 25 := by
  have hc : ((469827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((469827/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((469827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c26 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((283189/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 242173/1000000) (δ := 1791/200000000) (ψ := 343219/500000) 176 91
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t26 : ((138832548351/1250000000000 : ℚ) : ℝ) ≤ stT176 26 := by
  have hc : ((70791/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138832548351/1250000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((70791/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c27 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((240613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1659749/5000000) (δ := 8941/1000000000) (ψ := 343219/500000) 176 92
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t27 : ((925926987/20000000000 : ℚ) : ℝ) ≤ stT176 27 := by
  have hc : ((240563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((925926987/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((240563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c28 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((62569/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3613323/10000000) (δ := 4417/500000000) (ψ := 343219/500000) 176 93
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t28 : ((3693657099/156250000000 : ℚ) : ℝ) ≤ stT176 28 := by
  have hc : ((3909/31250 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3693657099/156250000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((3909/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c29 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((57623/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 836383/2500000) (δ := 2219/250000000) (ψ := 343219/500000) 176 94
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t29 : ((213959981613/5000000000000 : ℚ) : ℝ) ≤ stT176 29 := by
  have hc : ((115221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213959981613/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((115221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c30 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((130481/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2554229/10000000) (δ := 1123/125000000) (ψ := 343219/500000) 176 95
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t30 : ((476403379317/5000000000000 : ℚ) : ℝ) ≤ stT176 30 := by
  have hc : ((260937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((476403379317/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((260937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c31 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((34919/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1273821/10000000) (δ := 557/62500000) (ψ := 343219/500000) 176 96
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t31 : ((62712782601/400000000000 : ℚ) : ℝ) ≤ stT176 31 := by
  have hc : ((34917/40000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62712782601/400000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((34917/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c32 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((982773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232357/5000000) (δ := 1761/200000000) (ψ := 343219/500000) 176 97
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t32 : ((868612153409/5000000000000 : ℚ) : ℝ) ≤ stT176 32 := by
  have hc : ((982723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((868612153409/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((982723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c33 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((494733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2633173/10000000) (δ := 1781/200000000) (ψ := 343219/500000) 176 98
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t33 : ((107641536751/1250000000000 : ℚ) : ℝ) ≤ stT176 33 := by
  have hc : ((494683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107641536751/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((494683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c34 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-61189/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5205817/10000000) (δ := 8991/1000000000) (ψ := 343219/500000) 176 99
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t34 : ((-209897994033/2500000000000 : ℚ) : ℝ) ≤ stT176 34 := by
  have hc : ((-244781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209897994033/2500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-244781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c35 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-992553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7548683/10000000) (δ := 8991/1000000000) (ψ := 343219/500000) 176 99
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t35 : ((-1677805784327/10000000000000 : ℚ) : ℝ) ≤ stT176 35 := by
  have hc : ((-992603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1677805784327/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-992603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c36 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-15407/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1058979/2500000) (δ := 2221/250000000) (ψ := 343219/500000) 176 100
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t36 : ((-102755020551/5000000000000 : ℚ) : ℝ) ≤ stT176 36 := by
  have hc : ((-61653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102755020551/5000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-61653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c37 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((243221/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 583513/10000000) (δ := 8827/1000000000) (ψ := 343219/500000) 176 101
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t37 : ((799664197413/5000000000000 : ℚ) : ℝ) ≤ stT176 37 := by
  have hc : ((486417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((799664197413/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((486417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c38 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((13311/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1695221/5000000) (δ := 4467/500000000) (ψ := 343219/500000) 176 102
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t38 : ((86352884541/2500000000000 : ℚ) : ℝ) ≤ stT176 38 := by
  have hc : ((106463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86352884541/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((106463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c39 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-997269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3834593/5000000) (δ := 4481/500000000) (ψ := 343219/500000) 176 103
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t39 : ((-798494481479/5000000000000 : ℚ) : ℝ) ≤ stT176 39 := by
  have hc : ((-997319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-798494481479/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-997319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c40 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((90763/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1735323/5000000) (δ := 4481/500000000) (ψ := 343219/500000) 176 103
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t40 : ((35867324961/1250000000000 : ℚ) : ℝ) ≤ stT176 40 := by
  have hc : ((45369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35867324961/1250000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((45369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c41 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((106629/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1372573/10000000) (δ := 1771/200000000) (ψ := 343219/500000) 176 104
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t41 : ((666066774867/5000000000000 : ℚ) : ℝ) ≤ stT176 41 := by
  have hc : ((426491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((666066774867/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((426491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c42 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-426117/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -809699/1250000) (δ := 1771/200000000) (ψ := 343219/500000) 176 105
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t42 : ((-164387898707/1250000000000 : ℚ) : ℝ) ≤ stT176 42 := by
  have hc : ((-213071/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164387898707/1250000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-213071/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c43 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((1279/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 968957/2500000) (δ := 1771/200000000) (ψ := 343219/500000) 176 105
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t43 : ((3113104379/1000000000000 : ℚ) : ℝ) ≤ stT176 43 := by
  have hc : ((10207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3113104379/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((10207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c44 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((773341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -343351/2000000) (δ := 8963/1000000000) (ψ := 343219/500000) 176 106
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t44 : ((291444871699/2500000000000 : ℚ) : ℝ) ≤ stT176 44 := by
  have hc : ((773291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((291444871699/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((773291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c45 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-991957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7536687/10000000) (δ := 8933/1000000000) (ψ := 343219/500000) 176 107
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t45 : ((-184849592373/1250000000000 : ℚ) : ℝ) ≤ stT176 45 := by
  have hc : ((-992007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184849592373/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-992007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c46 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((328633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2134029/10000000) (δ := 8933/1000000000) (ψ := 343219/500000) 176 107
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t46 : ((15140808711/156250000000 : ℚ) : ℝ) ≤ stT176 46 := by
  have hc : ((10269/15625 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15140808711/156250000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((10269/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c47 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-36801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2055581/5000000) (δ := 4413/500000000) (ψ := 343219/500000) 176 108
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t47 : ((-537162449/50000000000 : ℚ) : ℝ) ≤ stT176 47 := by
  have hc : ((-18413/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-537162449/50000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-18413/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c48 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-470747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2576167/5000000) (δ := 4413/500000000) (ψ := 343219/500000) 176 108
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t48 : ((-42471068167/625000000000 : ℚ) : ℝ) ≤ stT176 48 := by
  have hc : ((-470797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42471068167/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-470797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c49 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((207279/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1483181/10000000) (δ := 2221/250000000) (ψ := 343219/500000) 176 109
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t49 : ((592189822343/5000000000000 : ℚ) : ℝ) ≤ stT176 49 := by
  have hc : ((414533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((592189822343/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((414533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c50 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-122999/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7406051/10000000) (δ := 2221/250000000) (ψ := 343219/500000) 176 109
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t50 : ((-347911493247/2500000000000 : ℚ) : ℝ) ≤ stT176 50 := by
  have hc : ((-492021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-347911493247/2500000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-492021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c51 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((493251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12851/312500) (δ := 8991/1000000000) (ψ := 343219/500000) 176 110
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t51 : ((8633181291/62500000000 : ℚ) : ℝ) ≤ stT176 51 := by
  have hc : ((246613/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8633181291/62500000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((246613/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c52 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-180909/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -52756/78125) (δ := 1781/200000000) (ψ := 343219/500000) 176 111
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t52 : ((-250889604169/2000000000000 : ℚ) : ℝ) ≤ stT176 52 := by
  have hc : ((-180919/200000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250889604169/2000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-180919/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c53 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((3181/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40711/250000) (δ := 1781/200000000) (ψ := 343219/500000) 176 111
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t53 : ((136536337/1250000000 : ℚ) : ℝ) ≤ stT176 53 := by
  have hc : ((497/625 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136536337/1250000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((497/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c54 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-696999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5854999/10000000) (δ := 4403/500000000) (ψ := 343219/500000) 176 112
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t54 : ((-237140949143/2500000000000 : ℚ) : ℝ) ≤ stT176 54 := by
  have hc : ((-697049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237140949143/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-697049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c55 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((315699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 443721/2000000) (δ := 4403/500000000) (ψ := 343219/500000) 176 112
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t55 : ((212827252963/2500000000000 : ℚ) : ℝ) ≤ stT176 55 := by
  have hc : ((157837/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212827252963/2500000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((157837/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c56 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-608121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2780609/5000000) (δ := 8913/1000000000) (ψ := 343219/500000) 176 113
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t56 : ((-812703164497/10000000000000 : ℚ) : ℝ) ≤ stT176 56 := by
  have hc : ((-608171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-812703164497/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-608171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c57 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((628913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1113303/5000000) (δ := 8913/1000000000) (ψ := 343219/500000) 176 113
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t57 : ((208237291779/2500000000000 : ℚ) : ℝ) ≤ stT176 57 := by
  have hc : ((628863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208237291779/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((628863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c58 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-344747/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2914483/5000000) (δ := 8983/1000000000) (ψ := 343219/500000) 176 114
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t58 : ((-22635402309/250000000000 : ℚ) : ℝ) ≤ stT176 58 := by
  have hc : ((-86193/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22635402309/250000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-86193/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c59 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((389719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 169257/1000000) (δ := 8983/1000000000) (ψ := 343219/500000) 176 114
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t59 : ((253669165983/2500000000000 : ℚ) : ℝ) ≤ stT176 59 := by
  have hc : ((194847/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((253669165983/2500000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((194847/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c60 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-880687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6620269/10000000) (δ := 2219/250000000) (ψ := 343219/500000) 176 115
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t60 : ((-227405412663/2000000000000 : ℚ) : ℝ) ≤ stT176 60 := by
  have hc : ((-880737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-227405412663/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-880737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c61 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((24153/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 652623/10000000) (δ := 2219/250000000) (ψ := 343219/500000) 176 115
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t61 : ((7730781961/62500000000 : ℚ) : ℝ) ≤ stT176 61 := by
  have hc : ((96607/100000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7730781961/62500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((96607/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c62 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-39993/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7807243/10000000) (δ := 2219/250000000) (ψ := 343219/500000) 176 115
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t62 : ((-5079372999/40000000000 : ℚ) : ℝ) ≤ stT176 62 := by
  have hc : ((-7999/8000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5079372999/40000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-7999/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c63 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((47067/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6723/78125) (δ := 4417/500000000) (ψ := 343219/500000) 176 116
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t63 : ((118591338649/1000000000000 : ℚ) : ℝ) ≤ stT176 63 := by
  have hc : ((94129/100000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118591338649/1000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((94129/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c64 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-755677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1517177/2500000) (δ := 4417/500000000) (ψ := 343219/500000) 176 116
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t64 : ((-944659505727/10000000000000 : ℚ) : ℝ) ≤ stT176 64 := by
  have hc : ((-755727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-944659505727/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-755727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c65 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((85881/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2817407/10000000) (δ := 4471/500000000) (ψ := 343219/500000) 176 117
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t65 : ((106509837237/2000000000000 : ℚ) : ℝ) ≤ stT176 65 := by
  have hc : ((85871/200000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106509837237/2000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((85871/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c66 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((10679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3900293/10000000) (δ := 4471/500000000) (ψ := 343219/500000) 176 117
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t66 : ((6541692453/5000000000000 : ℚ) : ℝ) ≤ stT176 66 := by
  have hc : ((10629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6541692453/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((10629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c67 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-242167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1038199/2000000) (δ := 4477/500000000) (ψ := 343219/500000) 176 118
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t67 : ((-3698559443/62500000000 : ℚ) : ℝ) ≤ stT176 67 := by
  have hc : ((-15137/31250 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3698559443/62500000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-15137/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c68 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((862271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1327649/10000000) (δ := 4477/500000000) (ψ := 343219/500000) 176 118
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t68 : ((522798218919/5000000000000 : ℚ) : ℝ) ≤ stT176 68 := by
  have hc : ((862221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((522798218919/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((862221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c69 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-499577/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7751121/10000000) (δ := 4477/500000000) (ψ := 343219/500000) 176 118
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t69 : ((-300725182059/2500000000000 : ℚ) : ℝ) ≤ stT176 69 := by
  have hc : ((-249801/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-300725182059/2500000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-249801/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c70 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((795887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -812907/5000000) (δ := 8847/1000000000) (ψ := 343219/500000) 176 119
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t70 : ((237801666459/2500000000000 : ℚ) : ℝ) ≤ stT176 70 := by
  have hc : ((795837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237801666459/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((795837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c71 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-271901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 461541/1000000) (δ := 8847/1000000000) (ψ := 343219/500000) 176 119
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t71 : ((-161373275841/5000000000000 : ℚ) : ℝ) ≤ stT176 71 := by
  have hc : ((-271951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161373275841/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-271951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c72 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-98421/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4938581/10000000) (δ := 8863/1000000000) (ψ := 343219/500000) 176 120
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t72 : ((-14500632619/312500000000 : ℚ) : ℝ) ≤ stT176 72 := by
  have hc : ((-196867/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14500632619/312500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-196867/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c73 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((899493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1130471/10000000) (δ := 8863/1000000000) (ψ := 343219/500000) 176 120
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t73 : ((1052717981073/10000000000000 : ℚ) : ℝ) ≤ stT176 73 := by
  have hc : ((899443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1052717981073/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((899443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c74 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-191371/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1423387/2000000) (δ := 8863/1000000000) (ψ := 343219/500000) 176 120
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t74 : ((-222476010737/2000000000000 : ℚ) : ℝ) ≤ stT176 74 := by
  have hc : ((-191381/200000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222476010737/2000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-191381/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c75 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((476659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41951/156250) (δ := 897/100000000) (ψ := 343219/500000) 176 121
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t75 : ((5503404123/100000000000 : ℚ) : ℝ) ≤ stT176 75 := by
  have hc : ((476609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5503404123/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((476609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c76 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((38559/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 196439/625000) (δ := 897/100000000) (ψ := 343219/500000) 176 121
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t76 : ((88446022729/2500000000000 : ℚ) : ℝ) ≤ stT176 76 := by
  have hc : ((154211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88446022729/2500000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((154211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c77 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-914589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -212913/312500) (δ := 4463/500000000) (ψ := 343219/500000) 176 122
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t77 : ((-521164046117/5000000000000 : ℚ) : ℝ) ≤ stT176 77 := by
  have hc : ((-914639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-521164046117/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-914639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c78 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((449287/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28393/250000) (δ := 4463/500000000) (ψ := 343219/500000) 176 122
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t78 : ((254344514787/2500000000000 : ℚ) : ℝ) ≤ stT176 78 := by
  have hc : ((224631/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254344514787/2500000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((224631/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c79 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-215281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13967/31250) (δ := 4463/500000000) (ψ := 343219/500000) 176 122
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t79 : ((-7570822629/312500000000 : ℚ) : ℝ) ≤ stT176 79 := by
  have hc : ((-215331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7570822629/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-215331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c80 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-326199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5703851/10000000) (δ := 4409/500000000) (ψ := 343219/500000) 176 123
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t80 : ((-11397797613/156250000000 : ℚ) : ℝ) ≤ stT176 80 := by
  have hc : ((-20389/31250 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11397797613/156250000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-20389/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c81 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((497737/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -237951/10000000) (δ := 4409/500000000) (ψ := 343219/500000) 176 123
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t81 : ((34563329877/312500000000 : ℚ) : ℝ) ≤ stT176 81 := by
  have hc : ((31107/31250 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34563329877/312500000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((31107/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c82 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-94753/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5160893/10000000) (δ := 4409/500000000) (ψ := 343219/500000) 176 123
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t82 : ((-26162074277/500000000000 : ℚ) : ℝ) ≤ stT176 82 := by
  have hc : ((-94763/200000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26162074277/500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-94763/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c83 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-123061/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2606827/5000000) (δ := 2223/250000000) (ψ := 343219/500000) 176 124
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t83 : ((-270181531521/5000000000000 : ℚ) : ℝ) ≤ stT176 83 := by
  have hc : ((-246147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-270181531521/5000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-246147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c84 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((3999/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13963/2500000) (δ := 4423/250000000) (ψ := 343219/500000) 176 124
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t84 : ((10907616733/100000000000 : ℚ) : ℝ) ≤ stT176 84 := by
  have hc : ((9997/10000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10907616733/100000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((9997/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c85 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-509331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 526301/1000000) (δ := 2223/250000000) (ψ := 343219/500000) 176 124
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t85 : ((-552501629793/10000000000000 : ℚ) : ℝ) ≤ stT176 85 := by
  have hc : ((-509381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-552501629793/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-509381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c86 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-521569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5298713/10000000) (δ := 8999/1000000000) (ψ := 343219/500000) 176 125
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t86 : ((-70309546629/1250000000000 : ℚ) : ℝ) ≤ stT176 86 := by
  have hc : ((-521619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70309546629/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-521619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c87 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((996409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -211917/10000000) (δ := 8999/1000000000) (ψ := 343219/500000) 176 125
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t87 : ((66763027513/625000000000 : ℚ) : ℝ) ≤ stT176 87 := by
  have hc : ((996359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66763027513/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((996359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c88 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-348423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4816711/10000000) (δ := 8999/1000000000) (ψ := 343219/500000) 176 125
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t88 : ((-92868402973/2500000000000 : ℚ) : ℝ) ≤ stT176 88 := by
  have hc : ((-348473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92868402973/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-348473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c89 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-357629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5919473/10000000) (δ := 8897/1000000000) (ψ := 343219/500000) 176 126
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t89 : ((-94778131173/1250000000000 : ℚ) : ℝ) ≤ stT176 89 := by
  have hc : ((-178827/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94778131173/1250000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-178827/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c90 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((920559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1003221/10000000) (δ := 8897/1000000000) (ψ := 343219/500000) 176 126
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t90 : ((242575293207/2500000000000 : ℚ) : ℝ) ≤ stT176 90 := by
  have hc : ((920509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242575293207/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((920509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c91 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((6827/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3858713/10000000) (δ := 17697/1000000000) (ψ := 343219/500000) 176 126
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t91 : ((3571765659/1250000000000 : ℚ) : ℝ) ≤ stT176 91 := by
  have hc : ((13629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3571765659/1250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((13629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c92 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-947521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1760117/2500000) (δ := 8813/1000000000) (ψ := 343219/500000) 176 127
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t92 : ((-987911940183/10000000000000 : ℚ) : ℝ) ≤ stT176 92 := by
  have hc : ((-947571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-987911940183/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-947571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c93 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((611003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -285459/1250000) (δ := 8813/1000000000) (ψ := 343219/500000) 176 127
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t93 : ((633528324303/10000000000000 : ℚ) : ℝ) ≤ stT176 93 := by
  have hc : ((610953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((633528324303/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((610953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c94 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((566203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 121113/500000) (δ := 8813/1000000000) (ψ := 343219/500000) 176 127
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t94 : ((583942093413/10000000000000 : ℚ) : ℝ) ≤ stT176 94 := by
  have hc : ((566153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((583942093413/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((566153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c95 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-952261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 442399/625000) (δ := 8813/1000000000) (ψ := 343219/500000) 176 127
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t95 : ((-977051087469/10000000000000 : ℚ) : ℝ) ≤ stT176 95 := by
  have hc : ((-952311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-977051087469/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-952311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c96 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-38077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4022207/10000000) (δ := 223/25000000) (ψ := 343219/500000) 176 128
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t96 : ((-38913216867/10000000000000 : ℚ) : ℝ) ≤ stT176 96 := by
  have hc : ((-38127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38913216867/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-38127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c97 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((976983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21497/400000) (δ := 223/25000000) (ψ := 343219/500000) 176 128
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t97 : ((495962506909/5000000000000 : ℚ) : ℝ) ≤ stT176 97 := by
  have hc : ((976933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((495962506909/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((976933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c98 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-434351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1010057/2000000) (δ := 223/25000000) (ψ := 343219/500000) 176 128
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t98 : ((-438811473353/10000000000000 : ℚ) : ℝ) ≤ stT176 98 := by
  have hc : ((-434401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-438811473353/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-434401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c99 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-157341/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6190623/10000000) (δ := 359/40000000) (ψ := 343219/500000) 176 129
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t99 : ((-79071867169/1000000000000 : ℚ) : ℝ) ≤ stT176 99 := by
  have hc : ((-157351/200000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79071867169/1000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-157351/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c100 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((95007/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1768491/10000000) (δ := 359/40000000) (ψ := 343219/500000) 176 129
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t100 : ((380002619997/5000000000000 : ℚ) : ℝ) ≤ stT176 100 := by
  have hc : ((380003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((380002619997/5000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((380003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c101 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((125719/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 521937/2000000) (δ := 359/40000000) (ψ := 343219/500000) 176 129
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t101 : ((250165237281/5000000000000 : ℚ) : ℝ) ≤ stT176 101 := by
  have hc : ((251413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250165237281/5000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((251413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c102 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-467291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6944697/10000000) (δ := 359/40000000) (ψ := 343219/500000) 176 129
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t102 : ((-28919500173/312500000000 : ℚ) : ℝ) ≤ stT176 102 := by
  have hc : ((-116829/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28919500173/312500000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-116829/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c103 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-215727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2235291/5000000) (δ := 2217/250000000) (ψ := 343219/500000) 176 130
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t103 : ((-21261155141/1000000000000 : ℚ) : ℝ) ≤ stT176 103 := by
  have hc : ((-215777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21261155141/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-215777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c104 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((996153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -109673/5000000) (δ := 2217/250000000) (ψ := 343219/500000) 176 130
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t104 : ((48837933987/500000000000 : ℚ) : ℝ) ≤ stT176 104 := by
  have hc : ((996103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48837933987/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((996103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c105 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-12847/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1995617/5000000) (δ := 2217/250000000) (ψ := 343219/500000) 176 130
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t105 : ((-1570224709/625000000000 : ℚ) : ℝ) ≤ stT176 105 := by
  have hc : ((-1609/62500 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1570224709/625000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-1609/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c106 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-496213/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7546101/10000000) (δ := 4421/500000000) (ψ := 343219/500000) 176 131
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t106 : ((-120497255517/1250000000000 : ℚ) : ℝ) ≤ stT176 106 := by
  have hc : ((-248119/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120497255517/1250000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-248119/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c107 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((203529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3414589/10000000) (δ := 4421/500000000) (ψ := 343219/500000) 176 131
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t107 : ((12294404659/625000000000 : ℚ) : ℝ) ≤ stT176 107 := by
  have hc : ((203479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12294404659/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((203479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c108 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((4817/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 678467/10000000) (δ := 4421/500000000) (ψ := 343219/500000) 176 131
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t108 : ((74158683/800000000 : ℚ) : ℝ) ≤ stT176 108 := by
  have hc : ((19267/20000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74158683/800000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((19267/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c109 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-15857/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4733771/10000000) (δ := 4421/500000000) (ψ := 343219/500000) 176 131
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t109 : ((-30381314613/1000000000000 : ℚ) : ℝ) ≤ stT176 109 := by
  have hc : ((-31719/100000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30381314613/1000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-31719/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c110 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-468083/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1738973/2500000) (δ := 8949/1000000000) (ψ := 343219/500000) 176 132
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t110 : ((-111580914501/1250000000000 : ℚ) : ℝ) ≤ stT176 110 := by
  have hc : ((-117027/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111580914501/1250000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-117027/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c111 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((74411/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -185871/625000) (δ := 8949/1000000000) (ψ := 343219/500000) 176 132
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t111 : ((70618229957/2000000000000 : ℚ) : ℝ) ≤ stT176 111 := by
  have hc : ((74401/200000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70618229957/2000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((74401/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c112 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((925327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 121531/1250000) (δ := 8949/1000000000) (ψ := 343219/500000) 176 132
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t112 : ((874304415347/10000000000000 : ℚ) : ℝ) ≤ stT176 112 := by
  have hc : ((925277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((874304415347/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((925277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c113 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-373303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 305213/625000) (δ := 8949/1000000000) (ψ := 343219/500000) 176 132
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t113 : ((-351221007513/10000000000000 : ℚ) : ℝ) ≤ stT176 113 := by
  have hc : ((-373353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-351221007513/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-373353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c114 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-233759/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1736973/2500000) (δ := 8947/1000000000) (ψ := 343219/500000) 176 133
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t114 : ((-218947114099/2500000000000 : ℚ) : ℝ) ≤ stT176 114 := by
  have hc : ((-467543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218947114099/2500000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-467543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c115 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((1009/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -388133/1250000) (δ := 8947/1000000000) (ψ := 343219/500000) 176 133
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t115 : ((3763003329/125000000000 : ℚ) : ℝ) ≤ stT176 115 := by
  have hc : ((32283/100000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3763003329/125000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((32283/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c116 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((960561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 88057/1250000) (δ := 8947/1000000000) (ψ := 343219/500000) 176 133
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t116 : ((222952852809/2500000000000 : ℚ) : ℝ) ≤ stT176 116 := by
  have hc : ((960511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222952852809/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((960511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c117 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-109961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 280083/625000) (δ := 8947/1000000000) (ψ := 343219/500000) 176 133
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t117 : ((-50841083493/2500000000000 : ℚ) : ℝ) ≤ stT176 117 := by
  have hc : ((-54993/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50841083493/2500000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-54993/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c118 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-494473/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7481927/10000000) (δ := 8839/1000000000) (ψ := 343219/500000) 176 134
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t118 : ((-9104449927/100000000000 : ℚ) : ℝ) ≤ stT176 118 := by
  have hc : ((-247249/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9104449927/100000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-247249/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c119 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((15803/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -753771/2000000) (δ := 8839/1000000000) (ψ := 343219/500000) 176 134
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t119 : ((14475119769/2500000000000 : ℚ) : ℝ) ≤ stT176 119 := by
  have hc : ((31581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14475119769/2500000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((31581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c120 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((999397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -86803/10000000) (δ := 8839/1000000000) (ψ := 343219/500000) 176 134
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t120 : ((91227389589/1000000000000 : ℚ) : ℝ) ≤ stT176 120 := by
  have hc : ((999347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91227389589/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((999347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c121 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((72211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3564669/10000000) (δ := 8839/1000000000) (ψ := 343219/500000) 176 134
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t121 : ((3281178537/250000000000 : ℚ) : ℝ) ≤ stT176 121 := by
  have hc : ((36093/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3281178537/250000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((36093/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c122 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-38581/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7186089/10000000) (δ := 8839/1000000000) (ψ := 343219/500000) 176 134
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t122 : ((-17465713857/200000000000 : ℚ) : ℝ) ≤ stT176 122 := by
  have hc : ((-38583/40000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17465713857/200000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-38583/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c123 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-78107/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2465011/5000000) (δ := 8871/1000000000) (ψ := 343219/500000) 176 135
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t123 : ((-7043575539/200000000000 : ℚ) : ℝ) ≤ stT176 123 := by
  have hc : ((-78117/200000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7043575539/200000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-78117/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c124 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((42707/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -683627/5000000) (δ := 8871/1000000000) (ψ := 343219/500000) 176 135
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t124 : ((38349751317/500000000000 : ℚ) : ℝ) ≤ stT176 124 := by
  have hc : ((85409/100000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38349751317/500000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((85409/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c125 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((129459/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1083457/5000000) (δ := 8871/1000000000) (ψ := 343219/500000) 176 135
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t125 : ((115782680723/2000000000000 : ℚ) : ℝ) ≤ stT176 125 := by
  have hc : ((129449/200000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115782680723/2000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((129449/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c126 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-160743/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2836461/5000000) (δ := 8871/1000000000) (ψ := 343219/500000) 176 135
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t126 : ((-286424826081/5000000000000 : ℚ) : ℝ) ≤ stT176 126 := by
  have hc : ((-321511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286424826081/5000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-321511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c127 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-434189/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6556797/10000000) (δ := 4489/500000000) (ψ := 343219/500000) 176 136
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t127 : ((-192651416199/2500000000000 : ℚ) : ℝ) ≤ stT176 127 := by
  have hc : ((-217107/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192651416199/2500000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-217107/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c128 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((64521/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3105789/10000000) (δ := 4489/500000000) (ψ := 343219/500000) 176 136
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t128 : ((57020176213/2000000000000 : ℚ) : ℝ) ≤ stT176 128 := by
  have hc : ((64511/200000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57020176213/2000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((64511/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c129 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((495951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 318379/10000000) (δ := 4489/500000000) (ψ := 343219/500000) 176 136
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t129 : ((4366380467/50000000000 : ℚ) : ℝ) ≤ stT176 129 := by
  have hc : ((247963/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4366380467/50000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((247963/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c130 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((84273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3716059/10000000) (δ := 4489/500000000) (ψ := 343219/500000) 176 136
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t130 : ((36934227967/5000000000000 : ℚ) : ℝ) ≤ stT176 130 := by
  have hc : ((84223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36934227967/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((84223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c131 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-238349/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1417547/2000000) (δ := 4489/500000000) (ψ := 343219/500000) 176 136
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t131 : ((-83303053743/1000000000000 : ℚ) : ℝ) ≤ stT176 131 := by
  have hc : ((-476723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83303053743/1000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-476723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c132 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-25659/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1054841/2000000) (δ := 4459/500000000) (ψ := 343219/500000) 176 137
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t132 : ((-44670974647/1000000000000 : ℚ) : ℝ) ≤ stT176 132 := by
  have hc : ((-51323/100000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44670974647/1000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-51323/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c133 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((354973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1953437/10000000) (δ := 4459/500000000) (ψ := 343219/500000) 176 137
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t133 : ((76944651333/1250000000000 : ℚ) : ℝ) ≤ stT176 133 := by
  have hc : ((88737/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76944651333/1250000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((88737/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c134 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((429629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1342449/10000000) (δ := 8859/500000000) (ψ := 343219/500000) 176 137
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t134 : ((23195071767/312500000000 : ℚ) : ℝ) ≤ stT176 134 := by
  have hc : ((107401/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23195071767/312500000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((107401/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c135 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-271291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4613827/10000000) (δ := 4459/500000000) (ψ := 343219/500000) 176 137
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t135 : ((-233533159083/10000000000000 : ℚ) : ℝ) ≤ stT176 135 := by
  have hc : ((-271341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233533159083/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-271341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c136 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-249999/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1961723/2500000) (δ := 8811/1000000000) (ψ := 343219/500000) 176 138
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t136 : ((-428766222339/5000000000000 : ℚ) : ℝ) ≤ stT176 136 := by
  have hc : ((-500023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-428766222339/5000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-500023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c137 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-137489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -288963/625000) (δ := 8811/1000000000) (ψ := 343219/500000) 176 138
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t137 : ((-29371546503/1250000000000 : ℚ) : ℝ) ≤ stT176 137 := by
  have hc : ((-68757/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29371546503/1250000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-68757/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c138 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((421121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71171/500000) (δ := 8811/1000000000) (ψ := 343219/500000) 176 138
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t138 : ((5600945259/78125000000 : ℚ) : ℝ) ≤ stT176 138 := by
  have hc : ((52637/62500 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5600945259/78125000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((52637/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c139 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((23873/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 219189/1250000) (δ := 8811/1000000000) (ψ := 343219/500000) 176 138
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t139 : ((80989867321/1250000000000 : ℚ) : ℝ) ≤ stT176 139 := by
  have hc : ((381943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80989867321/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((381943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c140 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-191141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1226913/2500000) (δ := 8811/1000000000) (ψ := 343219/500000) 176 138
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t140 : ((-16156490073/500000000000 : ℚ) : ℝ) ≤ stT176 140 := by
  have hc : ((-95583/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16156490073/500000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-95583/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c141 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-498627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1533731/2000000) (δ := 8899/1000000000) (ψ := 343219/500000) 176 139
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t141 : ((-13123149347/156250000000 : ℚ) : ℝ) ≤ stT176 141 := by
  have hc : ((-124663/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13123149347/156250000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-124663/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c142 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-250153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4559087/10000000) (δ := 8899/1000000000) (ψ := 343219/500000) 176 139
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t142 : ((-104982926973/5000000000000 : ℚ) : ℝ) ≤ stT176 142 := by
  have hc : ((-250203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104982926973/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-250203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c143 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((415877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1471343/10000000) (δ := 8899/1000000000) (ψ := 343219/500000) 176 139
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t143 : ((43469113523/625000000000 : ℚ) : ℝ) ≤ stT176 143 := by
  have hc : ((103963/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43469113523/625000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((103963/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c144 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((401663/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1594841/10000000) (δ := 8899/1000000000) (ψ := 343219/500000) 176 139
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t144 : ((167349099727/2500000000000 : ℚ) : ℝ) ≤ stT176 144 := by
  have hc : ((200819/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167349099727/2500000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((200819/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c145 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-2813/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4639861/10000000) (δ := 8899/1000000000) (ψ := 343219/500000) 176 139
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t145 : ((-934594057/40000000000 : ℚ) : ℝ) ≤ stT176 145 := by
  have hc : ((-5627/20000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-934594057/40000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-5627/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c146 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-124639/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7663937/10000000) (δ := 8899/1000000000) (ψ := 343219/500000) 176 139
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t146 : ((-206314313543/2500000000000 : ℚ) : ℝ) ≤ stT176 146 := by
  have hc : ((-498581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206314313543/2500000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-498581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c147 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-430869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5040631/10000000) (δ := 2249/250000000) (ψ := 343219/500000) 176 140
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t147 : ((-355416389253/10000000000000 : ℚ) : ℝ) ≤ stT176 147 := by
  have hc : ((-430919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-355416389253/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-430919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c148 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((340003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2057563/10000000) (δ := 2249/250000000) (ψ := 343219/500000) 176 140
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t148 : ((69864969033/1250000000000 : ℚ) : ℝ) ≤ stT176 148 := by
  have hc : ((169989/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69864969033/1250000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((169989/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c149 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((116891/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 905441/10000000) (δ := 2249/250000000) (ψ := 343219/500000) 176 140
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t149 : ((383022442509/5000000000000 : ℚ) : ℝ) ≤ stT176 149 := by
  have hc : ((467539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((383022442509/5000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((467539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c150 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((3921/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3848557/10000000) (δ := 2249/250000000) (ψ := 343219/500000) 176 140
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t150 : ((799094429/312500000000 : ℚ) : ℝ) ≤ stT176 150 := by
  have hc : ((15659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((799094429/312500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((15659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c151 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-226957/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6772181/10000000) (δ := 2249/250000000) (ψ := 343219/500000) 176 140
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t151 : ((-369410564871/5000000000000 : ℚ) : ℝ) ≤ stT176 151 := by
  have hc : ((-453939/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369410564871/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-453939/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c152 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-745839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3015737/5000000) (δ := 8889/1000000000) (ψ := 343219/500000) 176 141
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t152 : ((-151249133753/2500000000000 : ℚ) : ℝ) ≤ stT176 152 := by
  have hc : ((-745889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151249133753/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-745889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c153 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((307257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1573109/5000000) (δ := 8889/1000000000) (ψ := 343219/500000) 176 141
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t153 : ((62090528391/2500000000000 : ℚ) : ℝ) ≤ stT176 153 := by
  have hc : ((307207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62090528391/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((307207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c154 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((496873/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1119/40000) (δ := 8889/1000000000) (ψ := 343219/500000) 176 141
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t154 : ((12511595283/156250000000 : ℚ) : ℝ) ≤ stT176 154 := by
  have hc : ((31053/31250 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12511595283/156250000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((31053/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c155 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((258583/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51363/200000) (δ := 8889/1000000000) (ψ := 343219/500000) 176 141
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t155 : ((103839349101/2500000000000 : ℚ) : ℝ) ≤ stT176 155 := by
  have hc : ((129279/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103839349101/2500000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((129279/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c156 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-554949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2698873/5000000) (δ := 8889/1000000000) (ψ := 343219/500000) 176 141
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t156 : ((-444354954359/10000000000000 : ℚ) : ℝ) ≤ stT176 156 := by
  have hc : ((-554999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-444354954359/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-554999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c157 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-989919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1499741/2000000) (δ := 8821/1000000000) (ψ := 343219/500000) 176 142
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t157 : ((-790081389303/10000000000000 : ℚ) : ℝ) ≤ stT176 157 := by
  have hc : ((-989969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-790081389303/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-989969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c158 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-153113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4705057/10000000) (δ := 8821/1000000000) (ψ := 343219/500000) 176 142
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t158 : ((-30457540251/1250000000000 : ℚ) : ℝ) ≤ stT176 158 := by
  have hc : ((-76569/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30457540251/1250000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-76569/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c159 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((716793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1929009/10000000) (δ := 8821/1000000000) (ψ := 343219/500000) 176 142
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t159 : ((568413752893/10000000000000 : ℚ) : ℝ) ≤ stT176 159 := by
  have hc : ((716743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((568413752893/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((716743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c160 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((945443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 165923/2000000) (δ := 8821/1000000000) (ψ := 343219/500000) 176 142
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t160 : ((747398398617/10000000000000 : ℚ) : ℝ) ≤ stT176 160 := by
  have hc : ((945393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((747398398617/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((945393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c161 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((70951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 714207/2000000) (δ := 8821/1000000000) (ψ := 343219/500000) 176 142
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t161 : ((2794874493/250000000000 : ℚ) : ℝ) ≤ stT176 161 := by
  have hc : ((35463/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2794874493/250000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((35463/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c162 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-405953/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1259103/2000000) (δ := 8821/1000000000) (ψ := 343219/500000) 176 142
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t162 : ((-6379335303/100000000000 : ℚ) : ℝ) ≤ stT176 162 := by
  have hc : ((-202989/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6379335303/100000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-202989/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c163 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-448093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1676183/2500000) (δ := 279/31250000) (ψ := 343219/500000) 176 143
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t163 : ((-175496676399/2500000000000 : ℚ) : ℝ) ≤ stT176 163 := by
  have hc : ((-224059/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175496676399/2500000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-224059/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c164 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-17319/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1003401/2500000) (δ := 279/31250000) (ψ := 343219/500000) 176 143
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t164 : ((-211615499/78125000000 : ℚ) : ℝ) ≤ stT176 164 := by
  have hc : ((-542/15625 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-211615499/78125000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-542/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c165 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((429997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -334711/2500000) (δ := 279/31250000) (ψ := 343219/500000) 176 143
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t165 : ((41841542757/625000000000 : ℚ) : ℝ) ≤ stT176 165 := by
  have hc : ((107493/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41841542757/625000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((107493/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c166 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((863863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 164971/1250000) (δ := 279/31250000) (ψ := 343219/500000) 176 143
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t166 : ((13408969199/200000000000 : ℚ) : ℝ) ≤ stT176 166 := by
  have hc : ((863813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13408969199/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((863813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c167 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-1773/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 990613/2500000) (δ := 279/31250000) (ψ := 343219/500000) 176 143
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t167 : ((-86051647/78125000000 : ℚ) : ℝ) ≤ stT176 167 := by
  have hc : ((-7117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86051647/78125000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-7117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c168 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-874751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 411831/625000) (δ := 279/31250000) (ψ := 343219/500000) 176 143
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t168 : ((-674923843117/10000000000000 : ℚ) : ℝ) ≤ stT176 168 := by
  have hc : ((-874801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-674923843117/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-874801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c169 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-429201/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1626839/2500000) (δ := 1121/125000000) (ψ := 343219/500000) 176 144
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t169 : ((-165086972603/2500000000000 : ℚ) : ℝ) ≤ stT176 169 := by
  have hc : ((-214613/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165086972603/2500000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-214613/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c170 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((6201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61117/156250) (δ := 1121/125000000) (ψ := 343219/500000) 176 144
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t170 : ((1179398891/2500000000000 : ℚ) : ℝ) ≤ stT176 170 := by
  have hc : ((6151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1179398891/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((6151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c171 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((861623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -332711/2500000) (δ := 1121/125000000) (ψ := 343219/500000) 176 144
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t171 : ((658861242987/10000000000000 : ℚ) : ℝ) ≤ stT176 171 := by
  have hc : ((861573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((658861242987/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((861573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c172 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((88049/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19293/156250) (δ := 1121/125000000) (ψ := 343219/500000) 176 144
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t172 : ((4195802853/62500000000 : ℚ) : ℝ) ≤ stT176 172 := by
  have hc : ((22011/25000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4195802853/62500000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((22011/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c173 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((884/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 946369/2500000) (δ := 1121/125000000) (ψ := 343219/500000) 176 144
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t173 : ((4297586991/1000000000000 : ℚ) : ℝ) ≤ stT176 173 := by
  have hc : ((28263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4297586991/1000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((28263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c174 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-817931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 197547/312500) (δ := 1121/125000000) (ψ := 343219/500000) 176 144
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t174 : ((-620110578119/10000000000000 : ℚ) : ℝ) ≤ stT176 174 := by
  have hc : ((-817981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-620110578119/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-817981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c175 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-922761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6864951/10000000) (δ := 443/50000000) (ψ := 343219/500000) 176 145
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t175 : ((-697579596419/10000000000000 : ℚ) : ℝ) ≤ stT176 175 := by
  have hc : ((-922811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-697579596419/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-922811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c176 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-42871/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4357831/10000000) (δ := 443/50000000) (ψ := 343219/500000) 176 145
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t176 : ((-64649363493/5000000000000 : ℚ) : ℝ) ≤ stT176 176 := by
  have hc : ((-85767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64649363493/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-85767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c177 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((367221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1864879/10000000) (δ := 443/50000000) (ψ := 343219/500000) 176 145
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t177 : ((34500175577/625000000000 : ℚ) : ℝ) ≤ stT176 177 := by
  have hc : ((91799/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34500175577/625000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((91799/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c178 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((121249/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 613993/10000000) (δ := 443/50000000) (ψ := 343219/500000) 176 145
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t178 : ((363500798601/5000000000000 : ℚ) : ℝ) ≤ stT176 178 := by
  have hc : ((484971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((363500798601/5000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((484971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c179 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((332727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 615801/2000000) (δ := 443/50000000) (ψ := 343219/500000) 176 145
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t179 : ((49730886699/2000000000000 : ℚ) : ℝ) ≤ stT176 179 := by
  have hc : ((332677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49730886699/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((332677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c180 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-598239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1106049/2000000) (δ := 443/50000000) (ψ := 343219/500000) 176 145
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t180 : ((-111484573971/2500000000000 : ℚ) : ℝ) ≤ stT176 180 := by
  have hc : ((-598289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111484573971/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-598289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c181 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-998961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -774003/1000000) (δ := 177/20000000) (ψ := 343219/500000) 176 146
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t181 : ((-148511976249/2000000000000 : ℚ) : ℝ) ≤ stT176 181 := by
  have hc : ((-999011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148511976249/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-999011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c182 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-52739/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2657903/5000000) (δ := 177/20000000) (ψ := 343219/500000) 176 146
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t182 : ((-3909649/100000000 : ℚ) : ℝ) ≤ stT176 182 := by
  have hc : ((-6593/12500 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3909649/100000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-6593/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c183 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((397569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1452413/5000000) (δ := 177/20000000) (ψ := 343219/500000) 176 146
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t183 : ((293854392699/10000000000000 : ℚ) : ℝ) ≤ stT176 183 := by
  have hc : ((397519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((293854392699/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((397519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c184 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((489753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -253501/5000000) (δ := 177/20000000) (ψ := 343219/500000) 176 146
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t184 : ((1410280817/19531250000 : ℚ) : ℝ) ≤ stT176 184 := by
  have hc : ((15304/15625 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1410280817/19531250000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((15304/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c185 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((365457/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 938921/5000000) (δ := 177/20000000) (ψ := 343219/500000) 176 146
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t185 : ((16791920153/312500000000 : ℚ) : ℝ) ≤ stT176 185 := by
  have hc : ((45679/62500 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16791920153/312500000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((45679/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c186 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-128763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2124897/5000000) (δ := 177/20000000) (ψ := 343219/500000) 176 146
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t186 : ((-23612582217/2500000000000 : ℚ) : ℝ) ≤ stT176 186 := by
  have hc : ((-128813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23612582217/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-128813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c187 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-878557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3304537/5000000) (δ := 177/20000000) (ψ := 343219/500000) 176 146
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t187 : ((-642501576711/10000000000000 : ℚ) : ℝ) ≤ stT176 187 := by
  have hc : ((-878607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-642501576711/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-878607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c188 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-452227/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6752237/10000000) (δ := 8957/1000000000) (ψ := 343219/500000) 176 147
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t188 : ((-3298386899/50000000000 : ℚ) : ℝ) ≤ stT176 188 := by
  have hc : ((-113063/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3298386899/50000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-113063/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c189 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-195141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4417993/10000000) (δ := 8957/1000000000) (ψ := 343219/500000) 176 147
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t189 : ((-141980567063/10000000000000 : ℚ) : ℝ) ≤ stT176 189 := by
  have hc : ((-195191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141980567063/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-195191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c190 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((33431/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2096113/10000000) (δ := 8957/1000000000) (ψ := 343219/500000) 176 147
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t190 : ((12125787233/250000000000 : ℚ) : ℝ) ≤ stT176 190 := by
  have hc : ((66857/100000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12125787233/250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((66857/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c191 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((996351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 213623/10000000) (δ := 8957/1000000000) (ψ := 343219/500000) 176 147
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t191 : ((360448749887/5000000000000 : ℚ) : ℝ) ≤ stT176 191 := by
  have hc : ((996301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((360448749887/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((996301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c192 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((536507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2511259/10000000) (δ := 8957/1000000000) (ψ := 343219/500000) 176 147
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t192 : ((387154042959/10000000000000 : ℚ) : ℝ) ≤ stT176 192 := by
  have hc : ((536457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((387154042959/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((536457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c193 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-341011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4796971/10000000) (δ := 8957/1000000000) (ψ := 343219/500000) 176 147
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t193 : ((-30687645597/1250000000000 : ℚ) : ℝ) ≤ stT176 193 := by
  have hc : ((-341061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30687645597/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-341061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c194 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-951341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7070891/10000000) (δ := 8957/1000000000) (ψ := 343219/500000) 176 147
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t194 : ((-683059730969/10000000000000 : ℚ) : ℝ) ≤ stT176 194 := by
  have hc : ((-951391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-683059730969/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-951391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c195 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-415011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6374857/10000000) (δ := 8939/1000000000) (ψ := 343219/500000) 176 148
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t195 : ((-14860675257/250000000000 : ℚ) : ℝ) ≤ stT176 195 := by
  have hc : ((-103759/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14860675257/250000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-103759/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c196 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-78807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4124213/10000000) (δ := 8939/1000000000) (ψ := 343219/500000) 176 148
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t196 : ((-28163225551/5000000000000 : ℚ) : ℝ) ≤ stT176 196 := by
  have hc : ((-78857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28163225551/5000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-78857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c197 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((364477/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1885009/10000000) (δ := 8939/1000000000) (ψ := 343219/500000) 176 148
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t197 : ((6491527911/125000000000 : ℚ) : ℝ) ≤ stT176 197 := by
  have hc : ((91113/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6491527911/125000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((91113/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c198 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((990611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 342843/10000000) (δ := 8939/1000000000) (ψ := 343219/500000) 176 148
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t198 : ((703960995309/10000000000000 : ℚ) : ℝ) ≤ stT176 198 := by
  have hc : ((990561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((703960995309/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((990561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c199 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((520133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102379/400000) (δ := 8939/1000000000) (ψ := 343219/500000) 176 148
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t199 : ((368676957123/10000000000000 : ℚ) : ℝ) ≤ stT176 199 := by
  have hc : ((520083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((368676957123/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((520083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c200 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-41119/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 190599/400000) (δ := 8939/1000000000) (ψ := 343219/500000) 176 148
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t200 : ((-116319808607/5000000000000 : ℚ) : ℝ) ≤ stT176 200 := by
  have hc : ((-164501/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116319808607/5000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-164501/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c201 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-37467/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6959519/10000000) (δ := 8939/1000000000) (ψ := 343219/500000) 176 148
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t201 : ((-13214304637/200000000000 : ℚ) : ℝ) ≤ stT176 201 := by
  have hc : ((-37469/40000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13214304637/200000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-37469/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c202 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-217493/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -820607/1250000) (δ := 69/7812500) (ψ := 343219/500000) 176 149
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t202 : ((-153036434789/2500000000000 : ℚ) : ℝ) ≤ stT176 202 := by
  have hc : ((-435011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153036434789/2500000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-435011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c203 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-36987/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1098001/2500000) (δ := 69/7812500) (ψ := 343219/500000) 176 149
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t203 : ((-25966825411/2000000000000 : ℚ) : ℝ) ≤ stT176 203 := by
  have hc : ((-36997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25966825411/2000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-36997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c204 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((125581/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -557461/2500000) (δ := 69/7812500) (ψ := 343219/500000) 176 149
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t204 : ((4395863997/100000000000 : ℚ) : ℝ) ≤ stT176 204 := by
  have hc : ((125571/200000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4395863997/100000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((125571/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c205 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((99951/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19561/2500000) (δ := 69/7812500) (ψ := 343219/500000) 176 149
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t205 : ((3490264239/50000000000 : ℚ) : ℝ) ≤ stT176 205 := by
  have hc : ((49973/50000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3490264239/50000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((49973/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c206 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((169611/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 515721/2500000) (δ := 69/7812500) (ψ := 343219/500000) 176 149
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t206 : ((236329743401/5000000000000 : ℚ) : ℝ) ≤ stT176 206 := by
  have hc : ((339197/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((236329743401/5000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((339197/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c207 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-106453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1048407/2500000) (δ := 69/7812500) (ψ := 343219/500000) 176 149
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t207 : ((-74024803647/10000000000000 : ℚ) : ℝ) ≤ stT176 207 := by
  have hc : ((-106503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74024803647/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-106503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c208 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-204057/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 157853/250000) (δ := 69/7812500) (ψ := 343219/500000) 176 149
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t208 : ((-2210888963/39062500000 : ℚ) : ℝ) ≤ stT176 208 := by
  have hc : ((-408139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2210888963/39062500000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-408139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c209 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-487039/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1456703/2000000) (δ := 4439/500000000) (ψ := 343219/500000) 176 150
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t209 : ((-8422736869/125000000000 : ℚ) : ℝ) ≤ stT176 209 := by
  have hc : ((-60883/62500 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8422736869/125000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-60883/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c210 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-240813/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5183263/10000000) (δ := 4439/500000000) (ψ := 343219/500000) 176 150
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t210 : ((-41548528827/1250000000000 : ℚ) : ℝ) ≤ stT176 210 := by
  have hc : ((-120419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41548528827/1250000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-120419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c211 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((81861/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3092999/10000000) (δ := 4439/500000000) (ψ := 343219/500000) 176 150
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t211 : ((28173399579/1250000000000 : ℚ) : ℝ) ≤ stT176 211 := by
  have hc : ((163697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28173399579/1250000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((163697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c212 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((919081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -202527/2000000) (δ := 4439/500000000) (ψ := 343219/500000) 176 150
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t212 : ((315596164431/5000000000000 : ℚ) : ℝ) ≤ stT176 212 := by
  have hc : ((919031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((315596164431/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((919031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c213 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((455893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1057961/10000000) (δ := 4439/500000000) (ψ := 343219/500000) 176 150
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t213 : ((19522205199/312500000000 : ℚ) : ℝ) ≤ stT176 213 := by
  have hc : ((113967/125000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19522205199/312500000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((113967/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c214 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((158823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3118877/10000000) (δ := 4439/500000000) (ψ := 343219/500000) 176 150
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t214 : ((10855193083/500000000000 : ℚ) : ℝ) ≤ stT176 214 := by
  have hc : ((79399/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10855193083/500000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((79399/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c215 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-19081/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5170157/10000000) (δ := 4439/500000000) (ψ := 343219/500000) 176 150
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t215 : ((-2602902117/80000000000 : ℚ) : ℝ) ≤ stT176 215 := by
  have hc : ((-19083/40000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2602902117/80000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-19083/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c216 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-967203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7211933/10000000) (δ := 4439/500000000) (ψ := 343219/500000) 176 150
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t216 : ((-329066241371/5000000000000 : ℚ) : ℝ) ≤ stT176 216 := by
  have hc : ((-967253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-329066241371/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-967253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c217 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-849317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3231857/5000000) (δ := 4493/500000000) (ψ := 343219/500000) 176 151
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t217 : ((-115317708223/2000000000000 : ℚ) : ℝ) ≤ stT176 217 := by
  have hc : ((-849367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115317708223/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-849367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c218 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-204051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2220363/5000000) (δ := 4493/500000000) (ψ := 343219/500000) 176 151
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t218 : ((-69117374943/5000000000000 : ℚ) : ℝ) ≤ stT176 218 := by
  have hc : ((-204101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69117374943/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-204101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c219 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((564647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1213489/5000000) (δ := 4493/500000000) (ψ := 343219/500000) 176 151
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t219 : ((381519082989/10000000000000 : ℚ) : ℝ) ≤ stT176 219 := by
  have hc : ((564597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381519082989/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((564597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c220 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((492879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -211213/5000000) (δ := 4493/500000000) (ψ := 343219/500000) 176 151
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t220 : ((166140836973/2500000000000 : ℚ) : ℝ) ≤ stT176 220 := by
  have hc : ((246427/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166140836973/2500000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((246427/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c221 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((202121/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 786531/5000000) (δ := 4493/500000000) (ψ := 343219/500000) 176 151
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t221 : ((8497045557/156250000000 : ℚ) : ℝ) ≤ stT176 221 := by
  have hc : ((404217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8497045557/156250000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((404217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c222 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((146473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1779743/5000000) (δ := 4493/500000000) (ψ := 343219/500000) 176 151
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t222 : ((24568168747/2500000000000 : ℚ) : ℝ) ≤ stT176 222 := by
  have hc : ((146423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24568168747/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((146423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c223 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-600409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2768511/5000000) (δ := 4493/500000000) (ψ := 343219/500000) 176 151
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t223 : ((-8041947387/200000000000 : ℚ) : ℝ) ≤ stT176 223 := by
  have hc : ((-600459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8041947387/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-600459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c224 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-123789/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3752857/5000000) (δ := 4493/500000000) (ψ := 343219/500000) 176 151
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t224 : ((-165428582937/2500000000000 : ℚ) : ℝ) ≤ stT176 224 := by
  have hc : ((-495181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165428582937/2500000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-495181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c225 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-7993/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3121157/5000000) (δ := 891/100000000) (ψ := 343219/500000) 176 152
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t225 : ((-10658005329/200000000000 : ℚ) : ℝ) ≤ stT176 225 := by
  have hc : ((-15987/20000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10658005329/200000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-15987/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c226 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-72567/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -536389/1250000) (δ := 1771/100000000) (ψ := 343219/500000) 176 152
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t226 : ((-3017971567/312500000000 : ℚ) : ℝ) ≤ stT176 226 := by
  have hc : ((-4537/31250 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3017971567/312500000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-4537/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c227 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((147569/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -234849/1000000) (δ := 891/100000000) (ψ := 343219/500000) 176 152
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t227 : ((195873285699/5000000000000 : ℚ) : ℝ) ≤ stT176 227 := by
  have hc : ((295113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((195873285699/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((295113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c228 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((246573/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -207213/5000000) (δ := 891/100000000) (ψ := 343219/500000) 176 152
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t228 : ((163288636093/2500000000000 : ℚ) : ℝ) ≤ stT176 228 := by
  have hc : ((493121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163288636093/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((493121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c229 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((2057/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 151119/1000000) (δ := 891/100000000) (ψ := 343219/500000) 176 152
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t229 : ((1087376019/20000000000 : ℚ) : ℝ) ≤ stT176 229 := by
  have hc : ((3291/4000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1087376019/20000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((3291/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c230 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((49529/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1714201/5000000) (δ := 891/100000000) (ψ := 343219/500000) 176 152
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t230 : ((3265018977/250000000000 : ℚ) : ℝ) ≤ stT176 230 := by
  have hc : ((99033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3265018977/250000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((99033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c231 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-21387/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2668649/5000000) (δ := 891/100000000) (ψ := 343219/500000) 176 152
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t231 : ((-439779229/12500000000 : ℚ) : ℝ) ≤ stT176 231 := by
  have hc : ((-21389/40000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-439779229/12500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-21389/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c232 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-969791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3618961/5000000) (δ := 891/100000000) (ψ := 343219/500000) 176 152
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t232 : ((-636732621253/10000000000000 : ℚ) : ℝ) ≤ stT176 232 := by
  have hc : ((-969841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-636732621253/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-969841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c233 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-436233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6577557/10000000) (δ := 8803/1000000000) (ψ := 343219/500000) 176 153
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t233 : ((-71450553369/1250000000000 : ℚ) : ℝ) ≤ stT176 233 := by
  have hc : ((-218129/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71450553369/1250000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-218129/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c234 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-4714/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4693169/10000000) (δ := 8803/1000000000) (ψ := 343219/500000) 176 153
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t234 : ((-98628848433/5000000000000 : ℚ) : ℝ) ≤ stT176 234 := by
  have hc : ((-150873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98628848433/5000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-150873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c235 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((107403/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2816833/10000000) (δ := 8803/1000000000) (ψ := 343219/500000) 176 153
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t235 : ((17513457521/625000000000 : ℚ) : ℝ) ≤ stT176 235 := by
  have hc : ((214781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17513457521/625000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((214781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c236 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((928893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -948461/10000000) (δ := 8803/1000000000) (ψ := 343219/500000) 176 153
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t236 : ((9447262153/156250000000 : ℚ) : ℝ) ≤ stT176 236 := by
  have hc : ((928843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9447262153/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((928843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c237 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((233549/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 911991/10000000) (δ := 8803/1000000000) (ψ := 343219/500000) 176 153
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t237 : ((303396141537/5000000000000 : ℚ) : ℝ) ≤ stT176 237 := by
  have hc : ((467073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((303396141537/5000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((467073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c238 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((22419/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2764611/10000000) (δ := 8803/1000000000) (ψ := 343219/500000) 176 153
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t238 : ((29060885099/1000000000000 : ℚ) : ℝ) ≤ stT176 238 := by
  have hc : ((44833/100000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29060885099/1000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((44833/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c239 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-13481/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4609487/10000000) (δ := 8803/1000000000) (ψ := 343219/500000) 176 153
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t239 : ((-17443523049/1000000000000 : ℚ) : ℝ) ≤ stT176 239 := by
  have hc : ((-26967/100000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17443523049/1000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-26967/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c240 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-13214/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6446663/10000000) (δ := 8803/1000000000) (ψ := 343219/500000) 176 153
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t240 : ((-136481837877/2500000000000 : ℚ) : ℝ) ≤ stT176 240 := by
  have hc : ((-422873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136481837877/2500000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-422873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c241 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-492887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -371589/500000) (δ := 8907/1000000000) (ψ := 343219/500000) 176 154
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t241 : ((-19844544699/312500000000 : ℚ) : ℝ) ≤ stT176 241 := by
  have hc : ((-30807/31250 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19844544699/312500000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-30807/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c242 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-7793/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1402457/2500000) (δ := 8907/1000000000) (ψ := 343219/500000) 176 154
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t242 : ((-1603179837/40000000000 : ℚ) : ℝ) ≤ stT176 242 := by
  have hc : ((-62349/100000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1603179837/40000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-62349/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c243 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((13153/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18977/50000) (δ := 8907/1000000000) (ψ := 343219/500000) 176 154
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t243 : ((33718523/10000000000 : ℚ) : ℝ) ≤ stT176 243 := by
  have hc : ((26281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33718523/10000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((26281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c244 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((28001/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -248551/1250000) (δ := 8907/1000000000) (ψ := 343219/500000) 176 154
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t244 : ((2240563977/50000000000 : ℚ) : ℝ) ≤ stT176 244 := by
  have hc : ((27999/40000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2240563977/50000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((27999/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c245 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((997149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18883/1000000) (δ := 17707/1000000000) (ψ := 343219/500000) 176 154
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t245 : ((159255655181/2500000000000 : ℚ) : ℝ) ≤ stT176 245 := by
  have hc : ((997099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159255655181/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((997099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c246 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((100159/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 400861/2500000) (δ := 8907/1000000000) (ψ := 343219/500000) 176 154
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t246 : ((31927494867/625000000000 : ℚ) : ℝ) ≤ stT176 246 := by
  have hc : ((400611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31927494867/625000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((400611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c247 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((668/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 847109/2500000) (δ := 8907/1000000000) (ψ := 343219/500000) 176 154
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t247 : ((3399506341/250000000000 : ℚ) : ℝ) ≤ stT176 247 := by
  have hc : ((21371/100000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3399506341/250000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((21371/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c248 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-475637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1291553/2500000) (δ := 8907/1000000000) (ψ := 343219/500000) 176 154
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t248 : ((-302061720687/10000000000000 : ℚ) : ℝ) ≤ stT176 248 := by
  have hc : ((-475687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-302061720687/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-475687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c249 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-58341/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 433551/625000) (δ := 8907/1000000000) (ψ := 343219/500000) 176 154
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t249 : ((-11831721797/200000000000 : ℚ) : ℝ) ≤ stT176 249 := by
  have hc : ((-466753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11831721797/200000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-466753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_c250 :
    |Real.cos (((176 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-471617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -218987/312500) (δ := 8989/1000000000) (ψ := 343219/500000) 176 155
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st176_t250 : ((-18643300797/312500000000 : ℚ) : ℝ) ≤ stT176 250 := by
  have hc : ((-235821/250000 : ℚ) : ℝ)
      ≤ Real.cos (((176 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((343219/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st176_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18643300797/312500000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-235821/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st176_p1 : ((386729/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT176 (i+1) := by
  rw [Finset.sum_range_one]
  exact st176_t1

theorem st176_p2 : ((164650429237/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT176 (i+1))
      = (∑ i ∈ Finset.range 1, stT176 (i+1)) + stT176 2 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 1
    simpa using h
  have hprev := st176_p1
  have hstep := st176_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p3 : ((2306943188051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT176 (i+1))
      = (∑ i ∈ Finset.range 2, stT176 (i+1)) + stT176 3 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 2
    simpa using h
  have hprev := st176_p2
  have hstep := st176_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p4 : ((725309008393/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT176 (i+1))
      = (∑ i ∈ Finset.range 3, stT176 (i+1)) + stT176 4 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 3
    simpa using h
  have hprev := st176_p3
  have hstep := st176_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p5 : ((732380372697/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT176 (i+1))
      = (∑ i ∈ Finset.range 4, stT176 (i+1)) + stT176 5 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 4
    simpa using h
  have hprev := st176_p4
  have hstep := st176_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p6 : ((943377444779/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT176 (i+1))
      = (∑ i ∈ Finset.range 5, stT176 (i+1)) + stT176 6 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 5
    simpa using h
  have hprev := st176_p5
  have hstep := st176_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p7 : ((1280322188243/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT176 (i+1))
      = (∑ i ∈ Finset.range 6, stT176 (i+1)) + stT176 7 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 6
    simpa using h
  have hprev := st176_p6
  have hstep := st176_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p8 : ((8679816482557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT176 (i+1))
      = (∑ i ∈ Finset.range 7, stT176 (i+1)) + stT176 8 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 7
    simpa using h
  have hprev := st176_p7
  have hstep := st176_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p9 : ((5597652532791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT176 (i+1))
      = (∑ i ∈ Finset.range 8, stT176 (i+1)) + stT176 9 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 8
    simpa using h
  have hprev := st176_p8
  have hstep := st176_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p10 : ((25380720627/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT176 (i+1))
      = (∑ i ∈ Finset.range 9, stT176 (i+1)) + stT176 10 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 9
    simpa using h
  have hprev := st176_p9
  have hstep := st176_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p11 : ((5983827167541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT176 (i+1))
      = (∑ i ∈ Finset.range 10, stT176 (i+1)) + stT176 11 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 10
    simpa using h
  have hprev := st176_p10
  have hstep := st176_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p12 : ((3097779535029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT176 (i+1))
      = (∑ i ∈ Finset.range 11, stT176 (i+1)) + stT176 12 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 11
    simpa using h
  have hprev := st176_p11
  have hstep := st176_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p13 : ((22600550841/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT176 (i+1))
      = (∑ i ∈ Finset.range 12, stT176 (i+1)) + stT176 13 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 12
    simpa using h
  have hprev := st176_p12
  have hstep := st176_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p14 : ((492530053041/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT176 (i+1))
      = (∑ i ∈ Finset.range 13, stT176 (i+1)) + stT176 14 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 13
    simpa using h
  have hprev := st176_p13
  have hstep := st176_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p15 : ((3886201976547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT176 (i+1))
      = (∑ i ∈ Finset.range 14, stT176 (i+1)) + stT176 15 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 14
    simpa using h
  have hprev := st176_p14
  have hstep := st176_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p16 : ((1531131034519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT176 (i+1))
      = (∑ i ∈ Finset.range 15, stT176 (i+1)) + stT176 16 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 15
    simpa using h
  have hprev := st176_p15
  have hstep := st176_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p17 : ((745283469347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT176 (i+1))
      = (∑ i ∈ Finset.range 16, stT176 (i+1)) + stT176 17 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 16
    simpa using h
  have hprev := st176_p16
  have hstep := st176_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p18 : ((1460109316397/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT176 (i+1))
      = (∑ i ∈ Finset.range 17, stT176 (i+1)) + stT176 18 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 17
    simpa using h
  have hprev := st176_p17
  have hstep := st176_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p19 : ((684199845059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT176 (i+1))
      = (∑ i ∈ Finset.range 18, stT176 (i+1)) + stT176 19 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 18
    simpa using h
  have hprev := st176_p18
  have hstep := st176_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p20 : ((212592552411/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT176 (i+1))
      = (∑ i ∈ Finset.range 19, stT176 (i+1)) + stT176 20 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 19
    simpa using h
  have hprev := st176_p19
  have hstep := st176_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p21 : ((315672094597/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT176 (i+1))
      = (∑ i ∈ Finset.range 20, stT176 (i+1)) + stT176 21 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 20
    simpa using h
  have hprev := st176_p20
  have hstep := st176_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p22 : ((525664466921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT176 (i+1))
      = (∑ i ∈ Finset.range 21, stT176 (i+1)) + stT176 22 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 21
    simpa using h
  have hprev := st176_p21
  have hstep := st176_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p23 : ((329777605041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT176 (i+1))
      = (∑ i ∈ Finset.range 22, stT176 (i+1)) + stT176 23 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 22
    simpa using h
  have hprev := st176_p22
  have hstep := st176_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p24 : ((299629892109/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT176 (i+1))
      = (∑ i ∈ Finset.range 23, stT176 (i+1)) + stT176 24 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 23
    simpa using h
  have hprev := st176_p23
  have hstep := st176_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p25 : ((534543392109/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT176 (i+1))
      = (∑ i ∈ Finset.range 24, stT176 (i+1)) + stT176 25 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 24
    simpa using h
  have hprev := st176_p24
  have hstep := st176_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p26 : ((33668797023/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT176 (i+1))
      = (∑ i ∈ Finset.range 25, stT176 (i+1)) + stT176 26 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 25
    simpa using h
  have hprev := st176_p25
  have hstep := st176_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p27 : ((292498550859/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT176 (i+1))
      = (∑ i ∈ Finset.range 26, stT176 (i+1)) + stT176 27 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 26
    simpa using h
  have hprev := st176_p26
  have hstep := st176_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p28 : ((1521591267879/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT176 (i+1))
      = (∑ i ∈ Finset.range 27, stT176 (i+1)) + stT176 28 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 27
    simpa using h
  have hprev := st176_p27
  have hstep := st176_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p29 : ((3257142517371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT176 (i+1))
      = (∑ i ∈ Finset.range 28, stT176 (i+1)) + stT176 29 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 28
    simpa using h
  have hprev := st176_p28
  have hstep := st176_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p30 : ((233346618543/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT176 (i+1))
      = (∑ i ∈ Finset.range 29, stT176 (i+1)) + stT176 30 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 29
    simpa using h
  have hprev := st176_p29
  have hstep := st176_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p31 : ((9034911358401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT176 (i+1))
      = (∑ i ∈ Finset.range 30, stT176 (i+1)) + stT176 31 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 30
    simpa using h
  have hprev := st176_p30
  have hstep := st176_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p32 : ((10772135665219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT176 (i+1))
      = (∑ i ∈ Finset.range 31, stT176 (i+1)) + stT176 32 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 31
    simpa using h
  have hprev := st176_p31
  have hstep := st176_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p33 : ((11633267959227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT176 (i+1))
      = (∑ i ∈ Finset.range 32, stT176 (i+1)) + stT176 33 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 32
    simpa using h
  have hprev := st176_p32
  have hstep := st176_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p34 : ((2158735196619/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT176 (i+1))
      = (∑ i ∈ Finset.range 33, stT176 (i+1)) + stT176 34 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 33
    simpa using h
  have hprev := st176_p33
  have hstep := st176_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p35 : ((569741887423/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT176 (i+1))
      = (∑ i ∈ Finset.range 34, stT176 (i+1)) + stT176 35 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 34
    simpa using h
  have hprev := st176_p34
  have hstep := st176_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p36 : ((4455180078833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT176 (i+1))
      = (∑ i ∈ Finset.range 35, stT176 (i+1)) + stT176 36 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 35
    simpa using h
  have hprev := st176_p35
  have hstep := st176_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p37 : ((2627422138123/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT176 (i+1))
      = (∑ i ∈ Finset.range 36, stT176 (i+1)) + stT176 37 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 36
    simpa using h
  have hprev := st176_p36
  have hstep := st176_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p38 : ((339221877833/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT176 (i+1))
      = (∑ i ∈ Finset.range 37, stT176 (i+1)) + stT176 38 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 37
    simpa using h
  have hprev := st176_p37
  have hstep := st176_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p39 : ((4629055563849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT176 (i+1))
      = (∑ i ∈ Finset.range 38, stT176 (i+1)) + stT176 39 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 38
    simpa using h
  have hprev := st176_p38
  have hstep := st176_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p40 : ((4772524863693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT176 (i+1))
      = (∑ i ∈ Finset.range 39, stT176 (i+1)) + stT176 40 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 39
    simpa using h
  have hprev := st176_p39
  have hstep := st176_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p41 : ((33991197741/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT176 (i+1))
      = (∑ i ∈ Finset.range 40, stT176 (i+1)) + stT176 41 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 40
    simpa using h
  have hprev := st176_p40
  have hstep := st176_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p42 : ((1195260010933/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT176 (i+1))
      = (∑ i ∈ Finset.range 41, stT176 (i+1)) + stT176 42 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 41
    simpa using h
  have hprev := st176_p41
  have hstep := st176_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p43 : ((4796605565627/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT176 (i+1))
      = (∑ i ∈ Finset.range 42, stT176 (i+1)) + stT176 43 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 42
    simpa using h
  have hprev := st176_p42
  have hstep := st176_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p44 : ((215179812361/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT176 (i+1))
      = (∑ i ∈ Finset.range 43, stT176 (i+1)) + stT176 44 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 43
    simpa using h
  have hprev := st176_p43
  have hstep := st176_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p45 : ((4640096939533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT176 (i+1))
      = (∑ i ∈ Finset.range 44, stT176 (i+1)) + stT176 45 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 44
    simpa using h
  have hprev := st176_p44
  have hstep := st176_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p46 : ((1024920563657/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT176 (i+1))
      = (∑ i ∈ Finset.range 45, stT176 (i+1)) + stT176 46 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 45
    simpa using h
  have hprev := st176_p45
  have hstep := st176_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p47 : ((1014177314677/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT176 (i+1))
      = (∑ i ∈ Finset.range 46, stT176 (i+1)) + stT176 47 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 46
    simpa using h
  have hprev := st176_p46
  have hstep := st176_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p48 : ((4731118028049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT176 (i+1))
      = (∑ i ∈ Finset.range 47, stT176 (i+1)) + stT176 48 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 47
    simpa using h
  have hprev := st176_p47
  have hstep := st176_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p49 : ((665413481299/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT176 (i+1))
      = (∑ i ∈ Finset.range 48, stT176 (i+1)) + stT176 49 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 48
    simpa using h
  have hprev := st176_p48
  have hstep := st176_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p50 : ((2313742431949/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT176 (i+1))
      = (∑ i ∈ Finset.range 49, stT176 (i+1)) + stT176 50 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 49
    simpa using h
  have hprev := st176_p49
  have hstep := st176_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p51 : ((2659069683589/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT176 (i+1))
      = (∑ i ∈ Finset.range 50, stT176 (i+1)) + stT176 51 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 50
    simpa using h
  have hprev := st176_p50
  have hstep := st176_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p52 : ((9381830713511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT176 (i+1))
      = (∑ i ∈ Finset.range 51, stT176 (i+1)) + stT176 52 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 51
    simpa using h
  have hprev := st176_p51
  have hstep := st176_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p53 : ((10474121409511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT176 (i+1))
      = (∑ i ∈ Finset.range 52, stT176 (i+1)) + stT176 53 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 52
    simpa using h
  have hprev := st176_p52
  have hstep := st176_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p54 : ((9525557612939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT176 (i+1))
      = (∑ i ∈ Finset.range 53, stT176 (i+1)) + stT176 54 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 53
    simpa using h
  have hprev := st176_p53
  have hstep := st176_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p55 : ((10376866624791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT176 (i+1))
      = (∑ i ∈ Finset.range 54, stT176 (i+1)) + stT176 55 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 54
    simpa using h
  have hprev := st176_p54
  have hstep := st176_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p56 : ((4782081730147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT176 (i+1))
      = (∑ i ∈ Finset.range 55, stT176 (i+1)) + stT176 56 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 55
    simpa using h
  have hprev := st176_p55
  have hstep := st176_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p57 : ((1039711262741/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT176 (i+1))
      = (∑ i ∈ Finset.range 56, stT176 (i+1)) + stT176 57 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 56
    simpa using h
  have hprev := st176_p56
  have hstep := st176_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p58 : ((189833930701/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT176 (i+1))
      = (∑ i ∈ Finset.range 57, stT176 (i+1)) + stT176 58 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 57
    simpa using h
  have hprev := st176_p57
  have hstep := st176_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p59 : ((5253186599491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT176 (i+1))
      = (∑ i ∈ Finset.range 58, stT176 (i+1)) + stT176 59 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 58
    simpa using h
  have hprev := st176_p58
  have hstep := st176_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p60 : ((9369346135667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT176 (i+1))
      = (∑ i ∈ Finset.range 59, stT176 (i+1)) + stT176 60 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 59
    simpa using h
  have hprev := st176_p59
  have hstep := st176_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p61 : ((10606271249427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT176 (i+1))
      = (∑ i ∈ Finset.range 60, stT176 (i+1)) + stT176 61 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 60
    simpa using h
  have hprev := st176_p60
  have hstep := st176_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p62 : ((9336427999677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT176 (i+1))
      = (∑ i ∈ Finset.range 61, stT176 (i+1)) + stT176 62 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 61
    simpa using h
  have hprev := st176_p61
  have hstep := st176_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p63 : ((10522341386167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT176 (i+1))
      = (∑ i ∈ Finset.range 62, stT176 (i+1)) + stT176 63 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 62
    simpa using h
  have hprev := st176_p62
  have hstep := st176_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p64 : ((239442047011/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT176 (i+1))
      = (∑ i ∈ Finset.range 63, stT176 (i+1)) + stT176 64 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 63
    simpa using h
  have hprev := st176_p63
  have hstep := st176_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p65 : ((80881848533/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT176 (i+1))
      = (∑ i ∈ Finset.range 64, stT176 (i+1)) + stT176 65 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 64
    simpa using h
  have hprev := st176_p64
  have hstep := st176_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p66 : ((10123314451531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT176 (i+1))
      = (∑ i ∈ Finset.range 65, stT176 (i+1)) + stT176 66 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 65
    simpa using h
  have hprev := st176_p65
  have hstep := st176_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p67 : ((9531544940651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT176 (i+1))
      = (∑ i ∈ Finset.range 66, stT176 (i+1)) + stT176 67 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 66
    simpa using h
  have hprev := st176_p66
  have hstep := st176_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p68 : ((10577141378489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT176 (i+1))
      = (∑ i ∈ Finset.range 67, stT176 (i+1)) + stT176 68 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 67
    simpa using h
  have hprev := st176_p67
  have hstep := st176_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p69 : ((9374240650253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT176 (i+1))
      = (∑ i ∈ Finset.range 68, stT176 (i+1)) + stT176 69 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 68
    simpa using h
  have hprev := st176_p68
  have hstep := st176_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p70 : ((10325447316089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT176 (i+1))
      = (∑ i ∈ Finset.range 69, stT176 (i+1)) + stT176 70 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 69
    simpa using h
  have hprev := st176_p69
  have hstep := st176_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p71 : ((10002700764407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT176 (i+1))
      = (∑ i ∈ Finset.range 70, stT176 (i+1)) + stT176 71 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 70
    simpa using h
  have hprev := st176_p70
  have hstep := st176_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p72 : ((9538680520599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT176 (i+1))
      = (∑ i ∈ Finset.range 71, stT176 (i+1)) + stT176 72 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 71
    simpa using h
  have hprev := st176_p71
  have hstep := st176_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p73 : ((1323924812709/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT176 (i+1))
      = (∑ i ∈ Finset.range 72, stT176 (i+1)) + stT176 73 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 72
    simpa using h
  have hprev := st176_p72
  have hstep := st176_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p74 : ((9479018447987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT176 (i+1))
      = (∑ i ∈ Finset.range 73, stT176 (i+1)) + stT176 74 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 73
    simpa using h
  have hprev := st176_p73
  have hstep := st176_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p75 : ((10029358860287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT176 (i+1))
      = (∑ i ∈ Finset.range 74, stT176 (i+1)) + stT176 75 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 74
    simpa using h
  have hprev := st176_p74
  have hstep := st176_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p76 : ((10383142951203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT176 (i+1))
      = (∑ i ∈ Finset.range 75, stT176 (i+1)) + stT176 76 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 75
    simpa using h
  have hprev := st176_p75
  have hstep := st176_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p77 : ((9340814858969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT176 (i+1))
      = (∑ i ∈ Finset.range 76, stT176 (i+1)) + stT176 77 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 76
    simpa using h
  have hprev := st176_p76
  have hstep := st176_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p78 : ((10358192918117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT176 (i+1))
      = (∑ i ∈ Finset.range 77, stT176 (i+1)) + stT176 78 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 77
    simpa using h
  have hprev := st176_p77
  have hstep := st176_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p79 : ((10115926593989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT176 (i+1))
      = (∑ i ∈ Finset.range 78, stT176 (i+1)) + stT176 79 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 78
    simpa using h
  have hprev := st176_p78
  have hstep := st176_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p80 : ((9386467546757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT176 (i+1))
      = (∑ i ∈ Finset.range 79, stT176 (i+1)) + stT176 80 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 79
    simpa using h
  have hprev := st176_p79
  have hstep := st176_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p81 : ((10492494102821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT176 (i+1))
      = (∑ i ∈ Finset.range 80, stT176 (i+1)) + stT176 81 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 80
    simpa using h
  have hprev := st176_p80
  have hstep := st176_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p82 : ((9969252617281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT176 (i+1))
      = (∑ i ∈ Finset.range 81, stT176 (i+1)) + stT176 82 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 81
    simpa using h
  have hprev := st176_p81
  have hstep := st176_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p83 : ((9428889554239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT176 (i+1))
      = (∑ i ∈ Finset.range 82, stT176 (i+1)) + stT176 83 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 82
    simpa using h
  have hprev := st176_p82
  have hstep := st176_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p84 : ((10519651227539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT176 (i+1))
      = (∑ i ∈ Finset.range 83, stT176 (i+1)) + stT176 84 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 83
    simpa using h
  have hprev := st176_p83
  have hstep := st176_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p85 : ((4983574798873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT176 (i+1))
      = (∑ i ∈ Finset.range 84, stT176 (i+1)) + stT176 85 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 84
    simpa using h
  have hprev := st176_p84
  have hstep := st176_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p86 : ((4702336612357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT176 (i+1))
      = (∑ i ∈ Finset.range 85, stT176 (i+1)) + stT176 86 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 85
    simpa using h
  have hprev := st176_p85
  have hstep := st176_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p87 : ((5236440832461/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT176 (i+1))
      = (∑ i ∈ Finset.range 86, stT176 (i+1)) + stT176 87 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 86
    simpa using h
  have hprev := st176_p86
  have hstep := st176_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p88 : ((1010140805303/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT176 (i+1))
      = (∑ i ∈ Finset.range 87, stT176 (i+1)) + stT176 88 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 87
    simpa using h
  have hprev := st176_p87
  have hstep := st176_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p89 : ((4671591501823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT176 (i+1))
      = (∑ i ∈ Finset.range 88, stT176 (i+1)) + stT176 89 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 88
    simpa using h
  have hprev := st176_p88
  have hstep := st176_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p90 : ((5156742088237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT176 (i+1))
      = (∑ i ∈ Finset.range 89, stT176 (i+1)) + stT176 90 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 89
    simpa using h
  have hprev := st176_p89
  have hstep := st176_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p91 : ((5171029150873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT176 (i+1))
      = (∑ i ∈ Finset.range 90, stT176 (i+1)) + stT176 91 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 90
    simpa using h
  have hprev := st176_p90
  have hstep := st176_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p92 : ((9354146361563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT176 (i+1))
      = (∑ i ∈ Finset.range 91, stT176 (i+1)) + stT176 92 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 91
    simpa using h
  have hprev := st176_p91
  have hstep := st176_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p93 : ((4993837342933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT176 (i+1))
      = (∑ i ∈ Finset.range 92, stT176 (i+1)) + stT176 93 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 92
    simpa using h
  have hprev := st176_p92
  have hstep := st176_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p94 : ((10571616779279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT176 (i+1))
      = (∑ i ∈ Finset.range 93, stT176 (i+1)) + stT176 94 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 93
    simpa using h
  have hprev := st176_p93
  have hstep := st176_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p95 : ((959456569181/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT176 (i+1))
      = (∑ i ∈ Finset.range 94, stT176 (i+1)) + stT176 95 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 94
    simpa using h
  have hprev := st176_p94
  have hstep := st176_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p96 : ((9555652474943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT176 (i+1))
      = (∑ i ∈ Finset.range 95, stT176 (i+1)) + stT176 96 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 95
    simpa using h
  have hprev := st176_p95
  have hstep := st176_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p97 : ((10547577488761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT176 (i+1))
      = (∑ i ∈ Finset.range 96, stT176 (i+1)) + stT176 97 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 96
    simpa using h
  have hprev := st176_p96
  have hstep := st176_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p98 : ((631797875963/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT176 (i+1))
      = (∑ i ∈ Finset.range 97, stT176 (i+1)) + stT176 98 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 97
    simpa using h
  have hprev := st176_p97
  have hstep := st176_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p99 : ((4659023671859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT176 (i+1))
      = (∑ i ∈ Finset.range 98, stT176 (i+1)) + stT176 99 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 98
    simpa using h
  have hprev := st176_p98
  have hstep := st176_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p100 : ((314939143241/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT176 (i+1))
      = (∑ i ∈ Finset.range 99, stT176 (i+1)) + stT176 100 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 99
    simpa using h
  have hprev := st176_p99
  have hstep := st176_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p101 : ((5289191529137/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT176 (i+1))
      = (∑ i ∈ Finset.range 100, stT176 (i+1)) + stT176 101 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 100
    simpa using h
  have hprev := st176_p100
  have hstep := st176_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p102 : ((4826479526369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT176 (i+1))
      = (∑ i ∈ Finset.range 101, stT176 (i+1)) + stT176 102 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 101
    simpa using h
  have hprev := st176_p101
  have hstep := st176_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p103 : ((590021718833/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT176 (i+1))
      = (∑ i ∈ Finset.range 102, stT176 (i+1)) + stT176 103 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 102
    simpa using h
  have hprev := st176_p102
  have hstep := st176_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p104 : ((2604276545267/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT176 (i+1))
      = (∑ i ∈ Finset.range 103, stT176 (i+1)) + stT176 104 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 103
    simpa using h
  have hprev := st176_p103
  have hstep := st176_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p105 : ((2597995646431/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT176 (i+1))
      = (∑ i ∈ Finset.range 104, stT176 (i+1)) + stT176 105 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 104
    simpa using h
  have hprev := st176_p104
  have hstep := st176_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p106 : ((2357001135397/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT176 (i+1))
      = (∑ i ∈ Finset.range 105, stT176 (i+1)) + stT176 106 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 105
    simpa using h
  have hprev := st176_p105
  have hstep := st176_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p107 : ((2406178754033/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT176 (i+1))
      = (∑ i ∈ Finset.range 106, stT176 (i+1)) + stT176 107 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 106
    simpa using h
  have hprev := st176_p106
  have hstep := st176_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p108 : ((329740579801/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT176 (i+1))
      = (∑ i ∈ Finset.range 107, stT176 (i+1)) + stT176 108 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 107
    simpa using h
  have hprev := st176_p107
  have hstep := st176_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p109 : ((5123942703751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT176 (i+1))
      = (∑ i ∈ Finset.range 108, stT176 (i+1)) + stT176 109 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 108
    simpa using h
  have hprev := st176_p108
  have hstep := st176_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p110 : ((4677619045747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT176 (i+1))
      = (∑ i ∈ Finset.range 109, stT176 (i+1)) + stT176 110 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 109
    simpa using h
  have hprev := st176_p109
  have hstep := st176_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p111 : ((9708329241279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT176 (i+1))
      = (∑ i ∈ Finset.range 110, stT176 (i+1)) + stT176 111 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 110
    simpa using h
  have hprev := st176_p110
  have hstep := st176_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p112 : ((5291316828313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT176 (i+1))
      = (∑ i ∈ Finset.range 111, stT176 (i+1)) + stT176 112 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 111
    simpa using h
  have hprev := st176_p111
  have hstep := st176_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p113 : ((10231412649113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT176 (i+1))
      = (∑ i ∈ Finset.range 112, stT176 (i+1)) + stT176 113 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 112
    simpa using h
  have hprev := st176_p112
  have hstep := st176_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p114 : ((9355624192717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT176 (i+1))
      = (∑ i ∈ Finset.range 113, stT176 (i+1)) + stT176 114 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 113
    simpa using h
  have hprev := st176_p113
  have hstep := st176_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p115 : ((9656664459037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT176 (i+1))
      = (∑ i ∈ Finset.range 114, stT176 (i+1)) + stT176 115 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 114
    simpa using h
  have hprev := st176_p114
  have hstep := st176_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p116 : ((10548475870273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT176 (i+1))
      = (∑ i ∈ Finset.range 115, stT176 (i+1)) + stT176 116 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 115
    simpa using h
  have hprev := st176_p115
  have hstep := st176_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p117 : ((10345111536301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT176 (i+1))
      = (∑ i ∈ Finset.range 116, stT176 (i+1)) + stT176 117 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 116
    simpa using h
  have hprev := st176_p116
  have hstep := st176_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p118 : ((9434666543601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT176 (i+1))
      = (∑ i ∈ Finset.range 117, stT176 (i+1)) + stT176 118 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 117
    simpa using h
  have hprev := st176_p117
  have hstep := st176_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p119 : ((9492567022677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT176 (i+1))
      = (∑ i ∈ Finset.range 118, stT176 (i+1)) + stT176 119 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 118
    simpa using h
  have hprev := st176_p118
  have hstep := st176_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p120 : ((10404840918567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT176 (i+1))
      = (∑ i ∈ Finset.range 119, stT176 (i+1)) + stT176 120 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 119
    simpa using h
  have hprev := st176_p119
  have hstep := st176_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p121 : ((10536088060047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT176 (i+1))
      = (∑ i ∈ Finset.range 120, stT176 (i+1)) + stT176 121 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 120
    simpa using h
  have hprev := st176_p120
  have hstep := st176_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p122 : ((9662802367197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT176 (i+1))
      = (∑ i ∈ Finset.range 121, stT176 (i+1)) + stT176 122 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 121
    simpa using h
  have hprev := st176_p121
  have hstep := st176_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p123 : ((9310623590247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT176 (i+1))
      = (∑ i ∈ Finset.range 122, stT176 (i+1)) + stT176 123 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 122
    simpa using h
  have hprev := st176_p122
  have hstep := st176_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p124 : ((10077618616587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT176 (i+1))
      = (∑ i ∈ Finset.range 123, stT176 (i+1)) + stT176 124 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 123
    simpa using h
  have hprev := st176_p123
  have hstep := st176_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p125 : ((5328266010101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT176 (i+1))
      = (∑ i ∈ Finset.range 124, stT176 (i+1)) + stT176 125 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 124
    simpa using h
  have hprev := st176_p124
  have hstep := st176_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p126 : ((252092059201/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT176 (i+1))
      = (∑ i ∈ Finset.range 125, stT176 (i+1)) + stT176 126 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 125
    simpa using h
  have hprev := st176_p125
  have hstep := st176_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p127 : ((2328269175811/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT176 (i+1))
      = (∑ i ∈ Finset.range 126, stT176 (i+1)) + stT176 127 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 126
    simpa using h
  have hprev := st176_p126
  have hstep := st176_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p128 : ((9598177584309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT176 (i+1))
      = (∑ i ∈ Finset.range 127, stT176 (i+1)) + stT176 128 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 127
    simpa using h
  have hprev := st176_p127
  have hstep := st176_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p129 : ((10471453677709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT176 (i+1))
      = (∑ i ∈ Finset.range 128, stT176 (i+1)) + stT176 129 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 128
    simpa using h
  have hprev := st176_p128
  have hstep := st176_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p130 : ((10545322133643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT176 (i+1))
      = (∑ i ∈ Finset.range 129, stT176 (i+1)) + stT176 130 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 129
    simpa using h
  have hprev := st176_p129
  have hstep := st176_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p131 : ((9712291596213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT176 (i+1))
      = (∑ i ∈ Finset.range 130, stT176 (i+1)) + stT176 131 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 130
    simpa using h
  have hprev := st176_p130
  have hstep := st176_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p132 : ((9265581849743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT176 (i+1))
      = (∑ i ∈ Finset.range 131, stT176 (i+1)) + stT176 132 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 131
    simpa using h
  have hprev := st176_p131
  have hstep := st176_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p133 : ((9881139060407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT176 (i+1))
      = (∑ i ∈ Finset.range 132, stT176 (i+1)) + stT176 133 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 132
    simpa using h
  have hprev := st176_p132
  have hstep := st176_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p134 : ((10623381356951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT176 (i+1))
      = (∑ i ∈ Finset.range 133, stT176 (i+1)) + stT176 134 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 133
    simpa using h
  have hprev := st176_p133
  have hstep := st176_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p135 : ((2597462049467/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT176 (i+1))
      = (∑ i ∈ Finset.range 134, stT176 (i+1)) + stT176 135 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 134
    simpa using h
  have hprev := st176_p134
  have hstep := st176_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p136 : ((953231575319/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT176 (i+1))
      = (∑ i ∈ Finset.range 135, stT176 (i+1)) + stT176 136 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 135
    simpa using h
  have hprev := st176_p135
  have hstep := st176_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p137 : ((4648671690583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT176 (i+1))
      = (∑ i ∈ Finset.range 136, stT176 (i+1)) + stT176 137 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 136
    simpa using h
  have hprev := st176_p136
  have hstep := st176_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p138 : ((5007132187159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT176 (i+1))
      = (∑ i ∈ Finset.range 137, stT176 (i+1)) + stT176 138 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 137
    simpa using h
  have hprev := st176_p137
  have hstep := st176_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p139 : ((5331091656443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT176 (i+1))
      = (∑ i ∈ Finset.range 138, stT176 (i+1)) + stT176 139 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 138
    simpa using h
  have hprev := st176_p138
  have hstep := st176_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p140 : ((5169526755713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT176 (i+1))
      = (∑ i ∈ Finset.range 139, stT176 (i+1)) + stT176 140 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 139
    simpa using h
  have hprev := st176_p139
  have hstep := st176_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p141 : ((4749585976609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT176 (i+1))
      = (∑ i ∈ Finset.range 140, stT176 (i+1)) + stT176 141 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 140
    simpa using h
  have hprev := st176_p140
  have hstep := st176_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p142 : ((1161150762409/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT176 (i+1))
      = (∑ i ∈ Finset.range 141, stT176 (i+1)) + stT176 142 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 141
    simpa using h
  have hprev := st176_p141
  have hstep := st176_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p143 : ((249617797891/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT176 (i+1))
      = (∑ i ∈ Finset.range 142, stT176 (i+1)) + stT176 143 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 142
    simpa using h
  have hprev := st176_p142
  have hstep := st176_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p144 : ((2663527078637/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT176 (i+1))
      = (∑ i ∈ Finset.range 143, stT176 (i+1)) + stT176 144 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 143
    simpa using h
  have hprev := st176_p143
  have hstep := st176_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p145 : ((5210229900149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT176 (i+1))
      = (∑ i ∈ Finset.range 144, stT176 (i+1)) + stT176 145 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 144
    simpa using h
  have hprev := st176_p144
  have hstep := st176_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p146 : ((4797601273063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT176 (i+1))
      = (∑ i ∈ Finset.range 145, stT176 (i+1)) + stT176 146 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 145
    simpa using h
  have hprev := st176_p145
  have hstep := st176_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p147 : ((9239786156873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT176 (i+1))
      = (∑ i ∈ Finset.range 146, stT176 (i+1)) + stT176 147 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 146
    simpa using h
  have hprev := st176_p146
  have hstep := st176_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p148 : ((9798705909137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT176 (i+1))
      = (∑ i ∈ Finset.range 147, stT176 (i+1)) + stT176 148 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 147
    simpa using h
  have hprev := st176_p147
  have hstep := st176_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p149 : ((2112950158831/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT176 (i+1))
      = (∑ i ∈ Finset.range 148, stT176 (i+1)) + stT176 149 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 148
    simpa using h
  have hprev := st176_p148
  have hstep := st176_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p150 : ((10590321815883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT176 (i+1))
      = (∑ i ∈ Finset.range 149, stT176 (i+1)) + stT176 150 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 149
    simpa using h
  have hprev := st176_p149
  have hstep := st176_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p151 : ((9851500686141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT176 (i+1))
      = (∑ i ∈ Finset.range 150, stT176 (i+1)) + stT176 151 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 150
    simpa using h
  have hprev := st176_p150
  have hstep := st176_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p152 : ((9246504151129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT176 (i+1))
      = (∑ i ∈ Finset.range 151, stT176 (i+1)) + stT176 152 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 151
    simpa using h
  have hprev := st176_p151
  have hstep := st176_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p153 : ((9494866264693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT176 (i+1))
      = (∑ i ∈ Finset.range 152, stT176 (i+1)) + stT176 153 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 152
    simpa using h
  have hprev := st176_p152
  have hstep := st176_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p154 : ((2059121672561/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT176 (i+1))
      = (∑ i ∈ Finset.range 153, stT176 (i+1)) + stT176 154 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 153
    simpa using h
  have hprev := st176_p153
  have hstep := st176_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p155 : ((10710965759209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT176 (i+1))
      = (∑ i ∈ Finset.range 154, stT176 (i+1)) + stT176 155 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 154
    simpa using h
  have hprev := st176_p154
  have hstep := st176_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p156 : ((205332216097/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT176 (i+1))
      = (∑ i ∈ Finset.range 155, stT176 (i+1)) + stT176 156 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 155
    simpa using h
  have hprev := st176_p155
  have hstep := st176_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p157 : ((9476529415547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT176 (i+1))
      = (∑ i ∈ Finset.range 156, stT176 (i+1)) + stT176 157 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 156
    simpa using h
  have hprev := st176_p156
  have hstep := st176_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p158 : ((9232869093539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT176 (i+1))
      = (∑ i ∈ Finset.range 157, stT176 (i+1)) + stT176 158 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 157
    simpa using h
  have hprev := st176_p157
  have hstep := st176_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p159 : ((306290088951/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT176 (i+1))
      = (∑ i ∈ Finset.range 158, stT176 (i+1)) + stT176 159 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 158
    simpa using h
  have hprev := st176_p158
  have hstep := st176_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p160 : ((10548681245049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT176 (i+1))
      = (∑ i ∈ Finset.range 159, stT176 (i+1)) + stT176 160 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 159
    simpa using h
  have hprev := st176_p159
  have hstep := st176_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p161 : ((10660476224769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT176 (i+1))
      = (∑ i ∈ Finset.range 160, stT176 (i+1)) + stT176 161 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 160
    simpa using h
  have hprev := st176_p160
  have hstep := st176_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p162 : ((10022542694469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT176 (i+1))
      = (∑ i ∈ Finset.range 161, stT176 (i+1)) + stT176 162 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 161
    simpa using h
  have hprev := st176_p161
  have hstep := st176_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p163 : ((9320555988873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT176 (i+1))
      = (∑ i ∈ Finset.range 162, stT176 (i+1)) + stT176 163 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 162
    simpa using h
  have hprev := st176_p162
  have hstep := st176_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p164 : ((9293469205001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT176 (i+1))
      = (∑ i ∈ Finset.range 163, stT176 (i+1)) + stT176 164 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 163
    simpa using h
  have hprev := st176_p163
  have hstep := st176_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p165 : ((9962933889113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT176 (i+1))
      = (∑ i ∈ Finset.range 164, stT176 (i+1)) + stT176 165 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 164
    simpa using h
  have hprev := st176_p164
  have hstep := st176_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p166 : ((10633382349063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT176 (i+1))
      = (∑ i ∈ Finset.range 165, stT176 (i+1)) + stT176 166 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 165
    simpa using h
  have hprev := st176_p165
  have hstep := st176_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p167 : ((10622367738247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT176 (i+1))
      = (∑ i ∈ Finset.range 166, stT176 (i+1)) + stT176 167 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 166
    simpa using h
  have hprev := st176_p166
  have hstep := st176_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p168 : ((994744389513/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT176 (i+1))
      = (∑ i ∈ Finset.range 167, stT176 (i+1)) + stT176 168 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 167
    simpa using h
  have hprev := st176_p167
  have hstep := st176_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p169 : ((4643548002359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT176 (i+1))
      = (∑ i ∈ Finset.range 168, stT176 (i+1)) + stT176 169 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 168
    simpa using h
  have hprev := st176_p168
  have hstep := st176_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p170 : ((4645906800141/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT176 (i+1))
      = (∑ i ∈ Finset.range 169, stT176 (i+1)) + stT176 170 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 169
    simpa using h
  have hprev := st176_p169
  have hstep := st176_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p171 : ((9950674843269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT176 (i+1))
      = (∑ i ∈ Finset.range 170, stT176 (i+1)) + stT176 171 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 170
    simpa using h
  have hprev := st176_p170
  have hstep := st176_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p172 : ((10622003299749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT176 (i+1))
      = (∑ i ∈ Finset.range 171, stT176 (i+1)) + stT176 172 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 171
    simpa using h
  have hprev := st176_p171
  have hstep := st176_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p173 : ((10664979169659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT176 (i+1))
      = (∑ i ∈ Finset.range 172, stT176 (i+1)) + stT176 173 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 172
    simpa using h
  have hprev := st176_p172
  have hstep := st176_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p174 : ((502243429577/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT176 (i+1))
      = (∑ i ∈ Finset.range 173, stT176 (i+1)) + stT176 174 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 173
    simpa using h
  have hprev := st176_p173
  have hstep := st176_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p175 : ((9347288995121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT176 (i+1))
      = (∑ i ∈ Finset.range 174, stT176 (i+1)) + stT176 175 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 174
    simpa using h
  have hprev := st176_p174
  have hstep := st176_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p176 : ((1843598053627/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT176 (i+1))
      = (∑ i ∈ Finset.range 175, stT176 (i+1)) + stT176 176 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 175
    simpa using h
  have hprev := st176_p175
  have hstep := st176_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p177 : ((9769993077367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT176 (i+1))
      = (∑ i ∈ Finset.range 176, stT176 (i+1)) + stT176 177 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 176
    simpa using h
  have hprev := st176_p176
  have hstep := st176_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p178 : ((10496994674569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT176 (i+1))
      = (∑ i ∈ Finset.range 177, stT176 (i+1)) + stT176 178 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 177
    simpa using h
  have hprev := st176_p177
  have hstep := st176_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p179 : ((335801534627/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT176 (i+1))
      = (∑ i ∈ Finset.range 178, stT176 (i+1)) + stT176 179 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 178
    simpa using h
  have hprev := st176_p178
  have hstep := st176_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p180 : ((514985540609/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT176 (i+1))
      = (∑ i ∈ Finset.range 179, stT176 (i+1)) + stT176 180 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 179
    simpa using h
  have hprev := st176_p179
  have hstep := st176_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p181 : ((1911430186187/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT176 (i+1))
      = (∑ i ∈ Finset.range 180, stT176 (i+1)) + stT176 181 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 180
    simpa using h
  have hprev := st176_p180
  have hstep := st176_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p182 : ((1833237206187/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT176 (i+1))
      = (∑ i ∈ Finset.range 181, stT176 (i+1)) + stT176 182 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 181
    simpa using h
  have hprev := st176_p181
  have hstep := st176_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p183 : ((4730020211817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT176 (i+1))
      = (∑ i ∈ Finset.range 182, stT176 (i+1)) + stT176 183 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 182
    simpa using h
  have hprev := st176_p182
  have hstep := st176_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p184 : ((5091052100969/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT176 (i+1))
      = (∑ i ∈ Finset.range 183, stT176 (i+1)) + stT176 184 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 183
    simpa using h
  have hprev := st176_p183
  have hstep := st176_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p185 : ((5359722823417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT176 (i+1))
      = (∑ i ∈ Finset.range 184, stT176 (i+1)) + stT176 185 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 184
    simpa using h
  have hprev := st176_p184
  have hstep := st176_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p186 : ((5312497658983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT176 (i+1))
      = (∑ i ∈ Finset.range 185, stT176 (i+1)) + stT176 186 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 185
    simpa using h
  have hprev := st176_p185
  have hstep := st176_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p187 : ((1996498748251/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT176 (i+1))
      = (∑ i ∈ Finset.range 186, stT176 (i+1)) + stT176 187 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 186
    simpa using h
  have hprev := st176_p186
  have hstep := st176_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p188 : ((1864563272291/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT176 (i+1))
      = (∑ i ∈ Finset.range 187, stT176 (i+1)) + stT176 188 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 187
    simpa using h
  have hprev := st176_p187
  have hstep := st176_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p189 : ((1147604474299/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT176 (i+1))
      = (∑ i ∈ Finset.range 188, stT176 (i+1)) + stT176 189 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 188
    simpa using h
  have hprev := st176_p188
  have hstep := st176_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p190 : ((37757294077/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT176 (i+1))
      = (∑ i ∈ Finset.range 189, stT176 (i+1)) + stT176 190 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 189
    simpa using h
  have hprev := st176_p189
  have hstep := st176_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p191 : ((5193382391743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT176 (i+1))
      = (∑ i ∈ Finset.range 190, stT176 (i+1)) + stT176 191 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 190
    simpa using h
  have hprev := st176_p190
  have hstep := st176_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p192 : ((2154783765289/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT176 (i+1))
      = (∑ i ∈ Finset.range 191, stT176 (i+1)) + stT176 192 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 191
    simpa using h
  have hprev := st176_p191
  have hstep := st176_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p193 : ((10528417661669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT176 (i+1))
      = (∑ i ∈ Finset.range 192, stT176 (i+1)) + stT176 193 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 192
    simpa using h
  have hprev := st176_p192
  have hstep := st176_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p194 : ((98453579307/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT176 (i+1))
      = (∑ i ∈ Finset.range 193, stT176 (i+1)) + stT176 194 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 193
    simpa using h
  have hprev := st176_p193
  have hstep := st176_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p195 : ((462546546021/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT176 (i+1))
      = (∑ i ∈ Finset.range 194, stT176 (i+1)) + stT176 195 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 194
    simpa using h
  have hprev := st176_p194
  have hstep := st176_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p196 : ((4597302234659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT176 (i+1))
      = (∑ i ∈ Finset.range 195, stT176 (i+1)) + stT176 196 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 195
    simpa using h
  have hprev := st176_p195
  have hstep := st176_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p197 : ((4856963351099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT176 (i+1))
      = (∑ i ∈ Finset.range 196, stT176 (i+1)) + stT176 197 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 196
    simpa using h
  have hprev := st176_p196
  have hstep := st176_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p198 : ((10417887697507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT176 (i+1))
      = (∑ i ∈ Finset.range 197, stT176 (i+1)) + stT176 198 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 197
    simpa using h
  have hprev := st176_p197
  have hstep := st176_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p199 : ((1078656465463/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT176 (i+1))
      = (∑ i ∈ Finset.range 198, stT176 (i+1)) + stT176 199 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 198
    simpa using h
  have hprev := st176_p198
  have hstep := st176_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p200 : ((1319240629677/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT176 (i+1))
      = (∑ i ∈ Finset.range 199, stT176 (i+1)) + stT176 200 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 199
    simpa using h
  have hprev := st176_p199
  have hstep := st176_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p201 : ((4946604902783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT176 (i+1))
      = (∑ i ∈ Finset.range 200, stT176 (i+1)) + stT176 201 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 200
    simpa using h
  have hprev := st176_p200
  have hstep := st176_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p202 : ((928106406641/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT176 (i+1))
      = (∑ i ∈ Finset.range 201, stT176 (i+1)) + stT176 202 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 201
    simpa using h
  have hprev := st176_p201
  have hstep := st176_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p203 : ((1830245987871/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT176 (i+1))
      = (∑ i ∈ Finset.range 202, stT176 (i+1)) + stT176 203 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 202
    simpa using h
  have hprev := st176_p202
  have hstep := st176_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p204 : ((1918163267811/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT176 (i+1))
      = (∑ i ∈ Finset.range 203, stT176 (i+1)) + stT176 204 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 203
    simpa using h
  have hprev := st176_p203
  have hstep := st176_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p205 : ((2057773837371/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT176 (i+1))
      = (∑ i ∈ Finset.range 204, stT176 (i+1)) + stT176 205 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 204
    simpa using h
  have hprev := st176_p204
  have hstep := st176_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p206 : ((10761528673657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT176 (i+1))
      = (∑ i ∈ Finset.range 205, stT176 (i+1)) + stT176 206 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 205
    simpa using h
  have hprev := st176_p205
  have hstep := st176_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p207 : ((1068750387001/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT176 (i+1))
      = (∑ i ∈ Finset.range 206, stT176 (i+1)) + stT176 207 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 206
    simpa using h
  have hprev := st176_p206
  have hstep := st176_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p208 : ((5060758147741/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT176 (i+1))
      = (∑ i ∈ Finset.range 207, stT176 (i+1)) + stT176 208 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 207
    simpa using h
  have hprev := st176_p207
  have hstep := st176_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p209 : ((4723848672981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT176 (i+1))
      = (∑ i ∈ Finset.range 208, stT176 (i+1)) + stT176 209 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 208
    simpa using h
  have hprev := st176_p208
  have hstep := st176_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p210 : ((4557654557673/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT176 (i+1))
      = (∑ i ∈ Finset.range 209, stT176 (i+1)) + stT176 210 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 209
    simpa using h
  have hprev := st176_p209
  have hstep := st176_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p211 : ((4670348155989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT176 (i+1))
      = (∑ i ∈ Finset.range 210, stT176 (i+1)) + stT176 211 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 210
    simpa using h
  have hprev := st176_p210
  have hstep := st176_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p212 : ((249297216021/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT176 (i+1))
      = (∑ i ∈ Finset.range 211, stT176 (i+1)) + stT176 212 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 211
    simpa using h
  have hprev := st176_p211
  have hstep := st176_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p213 : ((1324574900901/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT176 (i+1))
      = (∑ i ∈ Finset.range 212, stT176 (i+1)) + stT176 213 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 212
    simpa using h
  have hprev := st176_p212
  have hstep := st176_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p214 : ((2703425767217/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT176 (i+1))
      = (∑ i ∈ Finset.range 213, stT176 (i+1)) + stT176 214 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 213
    simpa using h
  have hprev := st176_p213
  have hstep := st176_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p215 : ((10488340304243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT176 (i+1))
      = (∑ i ∈ Finset.range 214, stT176 (i+1)) + stT176 215 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 214
    simpa using h
  have hprev := st176_p214
  have hstep := st176_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p216 : ((9830207821501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT176 (i+1))
      = (∑ i ∈ Finset.range 215, stT176 (i+1)) + stT176 216 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 215
    simpa using h
  have hprev := st176_p215
  have hstep := st176_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p217 : ((4626809640193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT176 (i+1))
      = (∑ i ∈ Finset.range 216, stT176 (i+1)) + stT176 217 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 216
    simpa using h
  have hprev := st176_p216
  have hstep := st176_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p218 : ((18230769061/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT176 (i+1))
      = (∑ i ∈ Finset.range 217, stT176 (i+1)) + stT176 218 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 217
    simpa using h
  have hprev := st176_p217
  have hstep := st176_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p219 : ((9496903613489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT176 (i+1))
      = (∑ i ∈ Finset.range 218, stT176 (i+1)) + stT176 219 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 218
    simpa using h
  have hprev := st176_p218
  have hstep := st176_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p220 : ((10161466961381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT176 (i+1))
      = (∑ i ∈ Finset.range 219, stT176 (i+1)) + stT176 220 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 219
    simpa using h
  have hprev := st176_p219
  have hstep := st176_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p221 : ((10705277877029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT176 (i+1))
      = (∑ i ∈ Finset.range 220, stT176 (i+1)) + stT176 221 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 220
    simpa using h
  have hprev := st176_p220
  have hstep := st176_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p222 : ((10803550552017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT176 (i+1))
      = (∑ i ∈ Finset.range 221, stT176 (i+1)) + stT176 222 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 221
    simpa using h
  have hprev := st176_p221
  have hstep := st176_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p223 : ((10401453182667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT176 (i+1))
      = (∑ i ∈ Finset.range 222, stT176 (i+1)) + stT176 223 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 222
    simpa using h
  have hprev := st176_p222
  have hstep := st176_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p224 : ((9739738850919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT176 (i+1))
      = (∑ i ∈ Finset.range 223, stT176 (i+1)) + stT176 224 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 223
    simpa using h
  have hprev := st176_p223
  have hstep := st176_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p225 : ((9206838584469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT176 (i+1))
      = (∑ i ∈ Finset.range 224, stT176 (i+1)) + stT176 225 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 224
    simpa using h
  have hprev := st176_p224
  have hstep := st176_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p226 : ((364410539773/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT176 (i+1))
      = (∑ i ∈ Finset.range 225, stT176 (i+1)) + stT176 226 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 225
    simpa using h
  have hprev := st176_p225
  have hstep := st176_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p227 : ((9502010065723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT176 (i+1))
      = (∑ i ∈ Finset.range 226, stT176 (i+1)) + stT176 227 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 226
    simpa using h
  have hprev := st176_p226
  have hstep := st176_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p228 : ((2031032922019/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT176 (i+1))
      = (∑ i ∈ Finset.range 227, stT176 (i+1)) + stT176 228 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 227
    simpa using h
  have hprev := st176_p227
  have hstep := st176_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p229 : ((2139770523919/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT176 (i+1))
      = (∑ i ∈ Finset.range 228, stT176 (i+1)) + stT176 229 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 228
    simpa using h
  have hprev := st176_p228
  have hstep := st176_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p230 : ((433178135147/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT176 (i+1))
      = (∑ i ∈ Finset.range 229, stT176 (i+1)) + stT176 230 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 229
    simpa using h
  have hprev := st176_p229
  have hstep := st176_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p231 : ((419105199819/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT176 (i+1))
      = (∑ i ∈ Finset.range 230, stT176 (i+1)) + stT176 231 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 230
    simpa using h
  have hprev := st176_p230
  have hstep := st176_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p232 : ((4920448687111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT176 (i+1))
      = (∑ i ∈ Finset.range 231, stT176 (i+1)) + stT176 232 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 231
    simpa using h
  have hprev := st176_p231
  have hstep := st176_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p233 : ((926929294727/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT176 (i+1))
      = (∑ i ∈ Finset.range 232, stT176 (i+1)) + stT176 233 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 232
    simpa using h
  have hprev := st176_p232
  have hstep := st176_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p234 : ((2268008812601/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT176 (i+1))
      = (∑ i ∈ Finset.range 233, stT176 (i+1)) + stT176 234 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 233
    simpa using h
  have hprev := st176_p233
  have hstep := st176_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p235 : ((467612528537/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT176 (i+1))
      = (∑ i ∈ Finset.range 234, stT176 (i+1)) + stT176 235 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 234
    simpa using h
  have hprev := st176_p234
  have hstep := st176_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p236 : ((2489218837133/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT176 (i+1))
      = (∑ i ∈ Finset.range 235, stT176 (i+1)) + stT176 236 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 235
    simpa using h
  have hprev := st176_p235
  have hstep := st176_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p237 : ((5281833815803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT176 (i+1))
      = (∑ i ∈ Finset.range 236, stT176 (i+1)) + stT176 237 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 236
    simpa using h
  have hprev := st176_p236
  have hstep := st176_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p238 : ((2713569120649/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT176 (i+1))
      = (∑ i ∈ Finset.range 237, stT176 (i+1)) + stT176 238 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 237
    simpa using h
  have hprev := st176_p237
  have hstep := st176_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p239 : ((5339920626053/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT176 (i+1))
      = (∑ i ∈ Finset.range 238, stT176 (i+1)) + stT176 239 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 238
    simpa using h
  have hprev := st176_p238
  have hstep := st176_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p240 : ((5066956950299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT176 (i+1))
      = (∑ i ∈ Finset.range 239, stT176 (i+1)) + stT176 240 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 239
    simpa using h
  have hprev := st176_p239
  have hstep := st176_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p241 : ((949888847023/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT176 (i+1))
      = (∑ i ∈ Finset.range 240, stT176 (i+1)) + stT176 241 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 240
    simpa using h
  have hprev := st176_p240
  have hstep := st176_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p242 : ((454904675549/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT176 (i+1))
      = (∑ i ∈ Finset.range 241, stT176 (i+1)) + stT176 242 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 241
    simpa using h
  have hprev := st176_p241
  have hstep := st176_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p243 : ((456590601699/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT176 (i+1))
      = (∑ i ∈ Finset.range 242, stT176 (i+1)) + stT176 243 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 242
    simpa using h
  have hprev := st176_p242
  have hstep := st176_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p244 : ((478996241469/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT176 (i+1))
      = (∑ i ∈ Finset.range 243, stT176 (i+1)) + stT176 244 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 243
    simpa using h
  have hprev := st176_p243
  have hstep := st176_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p245 : ((1277118431263/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT176 (i+1))
      = (∑ i ∈ Finset.range 244, stT176 (i+1)) + stT176 245 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 244
    simpa using h
  have hprev := st176_p244
  have hstep := st176_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p246 : ((1340973420997/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT176 (i+1))
      = (∑ i ∈ Finset.range 245, stT176 (i+1)) + stT176 246 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 245
    simpa using h
  have hprev := st176_p245
  have hstep := st176_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p247 : ((678985476351/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT176 (i+1))
      = (∑ i ∈ Finset.range 246, stT176 (i+1)) + stT176 247 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 246
    simpa using h
  have hprev := st176_p246
  have hstep := st176_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p248 : ((10561705900929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT176 (i+1))
      = (∑ i ∈ Finset.range 247, stT176 (i+1)) + stT176 248 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 247
    simpa using h
  have hprev := st176_p247
  have hstep := st176_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p249 : ((9970119811079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT176 (i+1))
      = (∑ i ∈ Finset.range 248, stT176 (i+1)) + stT176 249 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 248
    simpa using h
  have hprev := st176_p248
  have hstep := st176_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_p250 : ((374941367423/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT176 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT176 (i+1))
      = (∑ i ∈ Finset.range 249, stT176 (i+1)) + stT176 250 := by
    have h := Finset.sum_range_succ (fun i => stT176 (i+1)) 249
    simpa using h
  have hprev := st176_p249
  have hstep := st176_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st176_s250 :
    |Real.sin (((176 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((343219/500000 : ℚ) : ℝ))
      - ((-10379/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -218987/312500) (δ := 8989/1000000000) (ψ := 343219/500000) 176 155
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 176`** (evaluated boundary). -/
theorem station_176_sign : hardyG ((((176:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 176 250 (by norm_num) (by norm_num)
    ((343219/500000 : ℚ) : ℝ)
  have hchain := st176_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT176 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((176 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((343219/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st176_c250
  have hsinb := abs_le.mp st176_s250
  have hbdy_lo : ((186312768103/6195250000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((176 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((343219/500000 : ℚ) : ℝ))) / 2
          - ((((176:ℕ)):ℝ))
            * Real.sin (((176 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((343219/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((176:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((176:ℝ) * Real.log (250:ℝ) - ((343219/500000 : ℚ) : ℝ))) / 2
        - ((176:ℝ)) * Real.sin ((176:ℝ) * Real.log (250:ℝ) - ((343219/500000 : ℚ) : ℝ))
        ≥ ((1472933/25000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((176:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((1472933/25000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((1472933/25000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((1472933/25000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((176:ℕ)):ℝ))+1) * (((((176:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((218691663421/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((374941367423/400000000000 : ℚ) : ℝ) + ((186312768103/6195250000000 : ℚ) : ℝ)
      - ((218691663421/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((343219/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((176:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((343219/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((176:ℕ)):ℝ)))).re
      - Real.sin ((343219/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((176:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((176:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((176:ℕ)):ℝ))
      = (((((176:ℕ)):ℝ)) * (Real.log ((((176:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((176:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_176
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
  have hθwin : |(((343219/500000 : ℚ) : ℝ) + ((33:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((176:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((176:ℕ)):ℝ)))
    (φ := ((343219/500000 : ℚ) : ℝ) + ((33:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((343219/500000 : ℚ) : ℝ) + ((33:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((343219/500000 : ℚ)) : ℝ) - Real.pi) + ((33:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((343219/500000 : ℚ)) : ℝ) - Real.pi) 33).1,
    (cos_sin_shift ((((343219/500000 : ℚ)) : ℝ) - Real.pi) 33).2]
  exact cos_sin_flip ((343219/500000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_176_sign
end AxiomAudit
