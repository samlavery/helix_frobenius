import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 293` (rung-309; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT293 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((293 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))

theorem st293_c1 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((1511/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1658271/5000000) (δ := 201/1000000000) (ψ := 1326617/1000000) 293 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t1 : ((12083/50000 : ℚ) : ℝ) ≤ stT293 1 := by
  have hc : ((12083/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12083/50000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((12083/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c2 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((762539/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 43973/250000) (δ := 3693/250000000) (ψ := 1326617/1000000) 293 32
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t2 : ((5391257252413/10000000000000 : ℚ) : ℝ) ≤ stT293 2 := by
  have hc : ((762439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5391257252413/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((762439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c3 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((496141/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 77701/2500000) (δ := 3667/250000000) (ψ := 1326617/1000000) 293 51
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t3 : ((1432091190341/2500000000000 : ℚ) : ℝ) ≤ stT293 3 := by
  have hc : ((496091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1432091190341/2500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((496091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c4 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-458993/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 341721/500000) (δ := 14761/1000000000) (ψ := 1326617/1000000) 293 64
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t4 : ((-2295215459043/5000000000000 : ℚ) : ℝ) ≤ stT293 4 := by
  have hc : ((-459043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2295215459043/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-459043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c5 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((270069/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2500489/10000000) (δ := 737/50000000) (ψ := 1326617/1000000) 293 75
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t5 : ((241512284113/1000000000000 : ℚ) : ℝ) ≤ stT293 5 := by
  have hc : ((270019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((241512284113/1000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((270019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c6 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-17223/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5386303/10000000) (δ := 7403/500000000) (ψ := 1326617/1000000) 293 83
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t6 : ((-562602899747/2500000000000 : ℚ) : ℝ) ≤ stT293 6 := by
  have hc : ((-137809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-562602899747/2500000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-137809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c7 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-9807/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1472403/2000000) (δ := 2931/200000000) (ψ := 1326617/1000000) 293 91
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t7 : ((-463384477/1250000000 : ℚ) : ℝ) ≤ stT293 7 := by
  have hc : ((-613/625 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-463384477/1250000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-613/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c8 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((12889/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -949511/2500000) (δ := 7349/500000000) (ψ := 1326617/1000000) 293 97
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t8 : ((710642133/39062500000 : ℚ) : ℝ) ≤ stT293 8 := by
  have hc : ((804/15625 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((710642133/39062500000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((804/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c9 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-2239/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3938187/10000000) (δ := 14669/1000000000) (ψ := 1326617/1000000) 293 102
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t9 : ((-3815000763/2500000000000 : ℚ) : ℝ) ≤ stT293 9 := by
  have hc : ((-2289/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3815000763/2500000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-2289/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c10 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((12871/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2574937/10000000) (δ := 1467/100000000) (ψ := 1326617/1000000) 293 107
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t10 : ((81387523149/500000000000 : ℚ) : ℝ) ≤ stT293 10 := by
  have hc : ((25737/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81387523149/500000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((25737/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c11 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-77661/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3075079/5000000) (δ := 14697/1000000000) (ψ := 1326617/1000000) 293 112
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t11 : ((-117093459747/500000000000 : ℚ) : ℝ) ≤ stT293 11 := by
  have hc : ((-77671/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117093459747/500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-77671/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c12 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-3147/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65577/125000) (δ := 7417/500000000) (ψ := 1326617/1000000) 293 116
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t12 : ((-2271603191/15625000000 : ℚ) : ℝ) ≤ stT293 12 := by
  have hc : ((-25181/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2271603191/15625000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-25181/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c13 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-803823/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6261227/10000000) (δ := 14847/1000000000) (ψ := 1326617/1000000) 293 119
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t13 : ((-2229681244423/10000000000000 : ℚ) : ℝ) ≤ stT293 13 := by
  have hc : ((-803923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2229681244423/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-803923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c14 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((305051/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -571629/2500000) (δ := 7409/500000000) (ψ := 1326617/1000000) 293 123
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t14 : ((203787333153/1250000000000 : ℚ) : ℝ) ≤ stT293 14 := by
  have hc : ((305001/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203787333153/1250000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((305001/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c15 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((900117/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 563447/5000000) (δ := 7353/500000000) (ψ := 1326617/1000000) 293 126
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t15 : ((580958273449/2500000000000 : ℚ) : ℝ) ≤ stT293 15 := by
  have hc : ((900017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((580958273449/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((900017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c16 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((174453/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 255491/2000000) (δ := 591/40000000) (ψ := 1326617/1000000) 293 129
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t16 : ((174433/800000 : ℚ) : ℝ) ≤ stT293 16 := by
  have hc : ((174433/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174433/800000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((174433/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c17 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((209721/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -287783/2000000) (δ := 7327/500000000) (ψ := 1326617/1000000) 293 132
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t17 : ((3973339467/19531250000 : ℚ) : ℝ) ≤ stT293 17 := by
  have hc : ((13106/15625 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3973339467/19531250000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((13106/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c18 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-447161/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6694277/10000000) (δ := 3683/250000000) (ψ := 1326617/1000000) 293 135
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t18 : ((-1054086612853/5000000000000 : ℚ) : ℝ) ≤ stT293 18 := by
  have hc : ((-447211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1054086612853/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-447211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c19 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((206671/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1494021/10000000) (δ := 2957/200000000) (ψ := 1326617/1000000) 293 137
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t19 : ((237039183711/1250000000000 : ℚ) : ℝ) ≤ stT293 19 := by
  have hc : ((103323/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237039183711/1250000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((103323/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c20 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-996687/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1912609/2500000) (δ := 3701/250000000) (ψ := 1326617/1000000) 293 139
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t20 : ((-557220878379/2500000000000 : ℚ) : ℝ) ≤ stT293 20 := by
  have hc : ((-996787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-557220878379/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-996787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c21 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((19217/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -466829/1250000) (δ := 7341/500000000) (ψ := 1326617/1000000) 293 142
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t21 : ((2617522511/156250000000 : ℚ) : ℝ) ≤ stT293 21 := by
  have hc : ((2399/31250 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2617522511/156250000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((2399/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c22 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((909023/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -537329/5000000) (δ := 2967/200000000) (ψ := 1326617/1000000) 293 144
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t22 : ((1937830198461/10000000000000 : ℚ) : ℝ) ≤ stT293 22 := by
  have hc : ((908923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1937830198461/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((908923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c23 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((249901/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 70359/10000000) (δ := 297/20000000) (ψ := 1326617/1000000) 293 146
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t23 : ((16282107567/78125000000 : ℚ) : ℝ) ≤ stT293 23 := by
  have hc : ((62469/62500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16282107567/78125000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((62469/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c24 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((997671/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -170661/10000000) (δ := 1833/125000000) (ψ := 1326617/1000000) 293 148
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t24 : ((2036282825611/10000000000000 : ℚ) : ℝ) ≤ stT293 24 := by
  have hc : ((997571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2036282825611/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((997571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c25 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((781463/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1684473/10000000) (δ := 593/40000000) (ψ := 1326617/1000000) 293 150
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t25 : ((781363/5000000 : ℚ) : ℝ) ≤ stT293 25 := by
  have hc : ((781363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((781363/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((781363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c26 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-44191/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1092809/2500000) (δ := 14793/1000000000) (ψ := 1326617/1000000) 293 152
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t26 : ((-5419671187/156250000000 : ℚ) : ℝ) ≤ stT293 26 := by
  have hc : ((-5527/31250 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5419671187/156250000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-5527/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c27 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-993353/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 756557/1000000) (δ := 14703/1000000000) (ψ := 1326617/1000000) 293 153
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t27 : ((-1911901291953/10000000000000 : ℚ) : ℝ) ≤ stT293 27 := by
  have hc : ((-993453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1911901291953/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-993453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c28 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((109911/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 348623/1250000) (δ := 7357/500000000) (ψ := 1326617/1000000) 293 155
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t28 : ((51916245073/625000000000 : ℚ) : ℝ) ≤ stT293 28 := by
  have hc : ((54943/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51916245073/625000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((54943/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c29 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((48881/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -584513/2000000) (δ := 14829/1000000000) (ψ := 1326617/1000000) 293 157
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t29 : ((181493015361/2500000000000 : ℚ) : ℝ) ≤ stT293 29 := by
  have hc : ((97737/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181493015361/2500000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((97737/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c30 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-157917/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 77529/125000) (δ := 14667/1000000000) (ψ := 1326617/1000000) 293 158
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t30 : ((-144176107127/1000000000000 : ℚ) : ℝ) ≤ stT293 30 := by
  have hc : ((-157937/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144176107127/1000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-157937/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c31 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((221979/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -239001/2000000) (δ := 14753/1000000000) (ψ := 1326617/1000000) 293 160
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t31 : ((199320573781/1250000000000 : ℚ) : ℝ) ≤ stT293 31 := by
  have hc : ((110977/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199320573781/1250000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((110977/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c32 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-51569/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1270591/2000000) (δ := 14757/1000000000) (ψ := 1326617/1000000) 293 161
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t32 : ((-364692099867/2500000000000 : ℚ) : ℝ) ≤ stT293 32 := by
  have hc : ((-206301/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364692099867/2500000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-206301/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c33 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((266307/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -100911/400000) (δ := 14731/1000000000) (ψ := 1326617/1000000) 293 163
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t33 : ((57936724429/625000000000 : ℚ) : ℝ) ≤ stT293 33 := by
  have hc : ((266257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57936724429/625000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((266257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c34 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((57951/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 454573/1250000) (δ := 1853/125000000) (ψ := 1326617/1000000) 293 164
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t34 : ((19859869297/1000000000000 : ℚ) : ℝ) ≤ stT293 34 := by
  have hc : ((57901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19859869297/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((57901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c35 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-216557/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3272999/5000000) (δ := 14793/1000000000) (ψ := 1326617/1000000) 293 166
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t35 : ((-183045251919/1250000000000 : ℚ) : ℝ) ≤ stT293 35 := by
  have hc : ((-108291/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183045251919/1250000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-108291/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c36 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((199397/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1618777/10000000) (δ := 37/2500000) (ψ := 1326617/1000000) 293 167
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t36 : ((41535816719/312500000000 : ℚ) : ℝ) ≤ stT293 36 := by
  have hc : ((49843/62500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41535816719/312500000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((49843/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c37 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((5701/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2743027/10000000) (δ := 3677/250000000) (ψ := 1326617/1000000) 293 168
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t37 : ((37481305211/500000000000 : ℚ) : ℝ) ≤ stT293 37 := by
  have hc : ((22799/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37481305211/500000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((22799/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c38 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-870891/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 82119/125000) (δ := 459/31250000) (ψ := 1326617/1000000) 293 169
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t38 : ((-282586933013/2000000000000 : ℚ) : ℝ) ≤ stT293 38 := by
  have hc : ((-870991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-282586933013/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-870991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c39 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-42919/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5819353/10000000) (δ := 7387/500000000) (ψ := 1326617/1000000) 293 171
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t39 : ((-137470860341/1250000000000 : ℚ) : ℝ) ≤ stT293 39 := by
  have hc : ((-171701/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137470860341/1250000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-171701/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c40 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((369049/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2982027/10000000) (δ := 3709/250000000) (ψ := 1326617/1000000) 293 172
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t40 : ((291679641981/5000000000000 : ℚ) : ℝ) ≤ stT293 40 := by
  have hc : ((368949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((291679641981/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((368949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c41 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((242771/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -602661/10000000) (δ := 1843/125000000) (ψ := 1326617/1000000) 293 173
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t41 : ((189552704901/1250000000000 : ℚ) : ℝ) ≤ stT293 41 := by
  have hc : ((121373/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189552704901/1250000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((121373/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c42 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((859581/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 335217/2500000) (δ := 14851/1000000000) (ψ := 1326617/1000000) 293 174
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t42 : ((1326207545873/10000000000000 : ℚ) : ℝ) ≤ stT293 42 := by
  have hc : ((859481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1326207545873/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((859481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c43 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((410679/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 573799/2000000) (δ := 2969/200000000) (ψ := 1326617/1000000) 293 175
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t43 : ((125225363263/2000000000000 : ℚ) : ℝ) ≤ stT293 43 := by
  have hc : ((410579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125225363263/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((410579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c44 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-923/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4000841/10000000) (δ := 2933/200000000) (ψ := 1326617/1000000) 293 176
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t44 : ((-11169489813/2500000000000 : ℚ) : ℝ) ≤ stT293 44 := by
  have hc : ((-7409/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11169489813/2500000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-7409/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c45 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-4061/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1188551/2500000) (δ := 3693/250000000) (ψ := 1326617/1000000) 293 177
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t45 : ((-3027822411/62500000000 : ℚ) : ℝ) ≤ stT293 45 := by
  have hc : ((-16249/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3027822411/62500000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-16249/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c46 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-234217/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1029157/2000000) (δ := 14779/1000000000) (ψ := 1326617/1000000) 293 178
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t46 : ((-17270397507/250000000000 : ℚ) : ℝ) ≤ stT293 46 := by
  have hc : ((-234267/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17270397507/250000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-234267/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c47 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-484401/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2595593/5000000) (δ := 3679/250000000) (ψ := 1326617/1000000) 293 179
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t47 : ((-14134347673/200000000000 : ℚ) : ℝ) ≤ stT293 47 := by
  have hc : ((-484501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14134347673/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-484501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c48 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-190621/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2452419/5000000) (δ := 14809/1000000000) (ψ := 1326617/1000000) 293 180
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t48 : ((-17200621581/312500000000 : ℚ) : ℝ) ≤ stT293 48 := by
  have hc : ((-190671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17200621581/312500000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-190671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c49 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-18603/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4300439/10000000) (δ := 7351/500000000) (ψ := 1326617/1000000) 293 181
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t49 : ((-13296791033/625000000000 : ℚ) : ℝ) ≤ stT293 49 := by
  have hc : ((-37231/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13296791033/625000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-37231/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c50 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((212747/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3391027/10000000) (δ := 3677/250000000) (ψ := 1326617/1000000) 293 182
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t50 : ((300728151811/10000000000000 : ℚ) : ℝ) ≤ stT293 50 := by
  have hc : ((212647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((300728151811/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((212647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c51 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((6407/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 547117/2500000) (δ := 459/31250000) (ψ := 1326617/1000000) 293 183
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t51 : ((112127421/1250000000 : ℚ) : ℝ) ≤ stT293 51 := by
  have hc : ((3203/5000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112127421/1250000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((3203/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c52 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((960583/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 704263/10000000) (δ := 367/25000000) (ψ := 1326617/1000000) 293 184
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t52 : ((5327799201/40000000000 : ℚ) : ℝ) ≤ stT293 52 := by
  have hc : ((960483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5327799201/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((960483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c53 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((912943/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -525447/5000000) (δ := 14773/1000000000) (ψ := 1326617/1000000) 293 185
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t53 : ((250777141803/2000000000000 : ℚ) : ℝ) ≤ stT293 53 := by
  have hc : ((912843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250777141803/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((912843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c54 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((84323/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1533447/5000000) (δ := 7383/500000000) (ψ := 1326617/1000000) 293 186
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t54 : ((57357497223/1250000000000 : ℚ) : ℝ) ≤ stT293 54 := by
  have hc : ((42149/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57357497223/1250000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((42149/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c55 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-533607/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5334141/10000000) (δ := 1843/125000000) (ψ := 1326617/1000000) 293 187
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t55 : ((-1799126297/25000000000 : ℚ) : ℝ) ≤ stT293 55 := by
  have hc : ((-533707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1799126297/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-533707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c56 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-999991/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7843553/10000000) (δ := 14751/1000000000) (ψ := 1326617/1000000) 293 188
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t56 : ((-1336428603937/10000000000000 : ℚ) : ℝ) ≤ stT293 56 := by
  have hc : ((-1000091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1336428603937/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-1000091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c57 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-114949/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1280351/2500000) (δ := 14751/1000000000) (ψ := 1326617/1000000) 293 188
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t57 : ((-76143428571/1250000000000 : ℚ) : ℝ) ≤ stT293 57 := by
  have hc : ((-57487/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76143428571/1250000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-57487/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c58 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((162887/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1076467/5000000) (δ := 7329/500000000) (ψ := 1326617/1000000) 293 189
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t58 : ((13365514323/156250000000 : ℚ) : ℝ) ≤ stT293 58 := by
  have hc : ((81431/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13365514323/156250000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((81431/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c59 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((915779/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1033381/10000000) (δ := 7383/500000000) (ψ := 1326617/1000000) 293 190
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t59 : ((1192112417631/10000000000000 : ℚ) : ℝ) ≤ stT293 59 := by
  have hc : ((915679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1192112417631/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((915679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c60 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-39981/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -69221/156250) (δ := 1473/100000000) (ψ := 1326617/1000000) 293 191
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t60 : ((-10328218199/400000000000 : ℚ) : ℝ) ≤ stT293 60 := by
  have hc : ((-40001/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10328218199/400000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-40001/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c61 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-997511/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 59981/78125) (δ := 1483/100000000) (ψ := 1326617/1000000) 293 191
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t61 : ((-1277310198459/10000000000000 : ℚ) : ℝ) ≤ stT293 61 := by
  have hc : ((-997611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1277310198459/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-997611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c62 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((18627/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3880421/10000000) (δ := 14823/1000000000) (ψ := 1326617/1000000) 293 192
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t62 : ((23529308527/10000000000000 : ℚ) : ℝ) ≤ stT293 62 := by
  have hc : ((18527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23529308527/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((18527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c63 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((24977/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -107249/10000000) (δ := 3679/250000000) (ψ := 1326617/1000000) 293 193
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t63 : ((62929796069/500000000000 : ℚ) : ℝ) ≤ stT293 63 := by
  have hc : ((49949/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62929796069/500000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((49949/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c64 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-140569/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2139791/5000000) (δ := 7397/500000000) (ψ := 1326617/1000000) 293 194
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t64 : ((-175836390669/10000000000000 : ℚ) : ℝ) ≤ stT293 64 := by
  have hc : ((-140669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175836390669/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-140669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c65 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-952121/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1769311/2500000) (δ := 14709/1000000000) (ψ := 1326617/1000000) 293 194
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t65 : ((-295271353227/2500000000000 : ℚ) : ℝ) ≤ stT293 65 := by
  have hc : ((-952221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-295271353227/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-952221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c66 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((522437/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102109/400000) (δ := 7401/500000000) (ψ := 1326617/1000000) 293 195
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t66 : ((321475963009/5000000000000 : ℚ) : ℝ) ≤ stT293 66 := by
  have hc : ((522337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((321475963009/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((522337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c67 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((655471/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2139977/10000000) (δ := 7347/500000000) (ψ := 1326617/1000000) 293 196
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t67 : ((400331409237/5000000000000 : ℚ) : ℝ) ≤ stT293 67 := by
  have hc : ((655371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((400331409237/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((655371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c68 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-941669/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6995879/10000000) (δ := 463/31250000) (ψ := 1326617/1000000) 293 197
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t68 : ((-1142063489151/10000000000000 : ℚ) : ℝ) ≤ stT293 68 := by
  have hc : ((-941769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1142063489151/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-941769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c69 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((91571/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1848871/5000000) (δ := 463/31250000) (ψ := 1326617/1000000) 293 197
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t69 : ((55059047559/5000000000000 : ℚ) : ℝ) ≤ stT293 69 := by
  have hc : ((91471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55059047559/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((91471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c70 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((831941/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1470499/10000000) (δ := 367/25000000) (ψ := 1326617/1000000) 293 198
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t70 : ((248559913687/2500000000000 : ℚ) : ℝ) ≤ stT293 70 := by
  have hc : ((831841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((248559913687/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((831841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c71 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-113813/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6788243/10000000) (δ := 14773/1000000000) (ψ := 1326617/1000000) 293 199
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t71 : ((-135086054541/1250000000000 : ℚ) : ℝ) ≤ stT293 71 := by
  have hc : ((-227651/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135086054541/1250000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-227651/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c72 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((187/1000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1728361/5000000) (δ := 14673/1000000000) (ψ := 1326617/1000000) 293 199
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t72 : ((2202637059/100000000000 : ℚ) : ℝ) ≤ stT293 72 := by
  have hc : ((1869/10000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2202637059/100000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((1869/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c73 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((13063/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2147649/10000000) (δ := 7333/500000000) (ψ := 1326617/1000000) 293 200
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t73 : ((15286738071/200000000000 : ℚ) : ℝ) ≤ stT293 73 := by
  have hc : ((13061/20000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15286738071/200000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((13061/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c74 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-999899/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7818453/10000000) (δ := 7333/500000000) (ψ := 1326617/1000000) 293 200
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t74 : ((-1162475837523/10000000000000 : ℚ) : ℝ) ≤ stT293 74 := by
  have hc : ((-999999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1162475837523/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-999999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c75 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((142581/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1942911/10000000) (δ := 2969/200000000) (ψ := 1326617/1000000) 293 201
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t75 : ((1646151867/20000000000 : ℚ) : ℝ) ≤ stT293 75 := by
  have hc : ((142561/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1646151867/20000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((142561/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c76 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-27177/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -126967/312500) (δ := 14751/1000000000) (ψ := 1326617/1000000) 293 202
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t76 : ((-31231519933/5000000000000 : ℚ) : ℝ) ≤ stT293 76 := by
  have hc : ((-27227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31231519933/5000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-27227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c77 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-296247/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5512369/10000000) (δ := 14851/1000000000) (ψ := 1326617/1000000) 293 202
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t77 : ((-168830919491/2500000000000 : ℚ) : ℝ) ≤ stT293 77 := by
  have hc : ((-296297/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168830919491/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-296297/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c78 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((47803/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -743853/10000000) (δ := 14759/1000000000) (ψ := 1326617/1000000) 293 203
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t78 : ((27060288023/250000000000 : ℚ) : ℝ) ≤ stT293 78 := by
  have hc : ((23899/25000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27060288023/250000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((23899/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c79 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-239317/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7120499/10000000) (δ := 7333/500000000) (ψ := 1326617/1000000) 293 204
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t79 : ((-4207512689/39062500000 : ℚ) : ℝ) ≤ stT293 79 := by
  have hc : ((-119671/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4207512689/39062500000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-119671/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c80 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((133881/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65421/312500) (δ := 7333/500000000) (ψ := 1326617/1000000) 293 204
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t80 : ((149661015413/2000000000000 : ℚ) : ℝ) ≤ stT293 80 := by
  have hc : ((133861/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149661015413/2000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((133861/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c81 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-46609/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -451501/1000000) (δ := 14673/1000000000) (ψ := 1326617/1000000) 293 205
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t81 : ((-6476255181/250000000000 : ℚ) : ℝ) ≤ stT293 81 := by
  have hc : ((-46629/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6476255181/250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-46629/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c82 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-6769/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2236419/5000000) (δ := 1473/100000000) (ψ := 1326617/1000000) 293 205
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t82 : ((-14957131983/625000000000 : ℚ) : ℝ) ≤ stT293 82 := by
  have hc : ((-54177/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14957131983/625000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-54177/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c83 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((587783/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11781/50000) (δ := 14823/1000000000) (ψ := 1326617/1000000) 293 206
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t83 : ((322532771743/5000000000000 : ℚ) : ℝ) ≤ stT293 83 := by
  have hc : ((587683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((322532771743/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((587683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c84 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-839159/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 641633/1000000) (δ := 29423/1000000000) (ψ := 1326617/1000000) 293 206
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t84 : ((-91570710231/1000000000000 : ℚ) : ℝ) ≤ stT293 84 := by
  have hc : ((-839259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91570710231/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-839259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c85 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((6057/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -311449/5000000) (δ := 3697/250000000) (ψ := 1326617/1000000) 293 207
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t85 : ((13138118513/125000000000 : ℚ) : ℝ) ≤ stT293 85 := by
  have hc : ((48451/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13138118513/125000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((48451/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c86 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-499673/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3881771/5000000) (δ := 1851/125000000) (ψ := 1326617/1000000) 293 208
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t86 : ((-67358162893/625000000000 : ℚ) : ℝ) ≤ stT293 86 := by
  have hc : ((-499723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67358162893/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-499723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c87 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((960521/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 352409/5000000) (δ := 2959/200000000) (ψ := 1326617/1000000) 293 208
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t87 : ((64354929947/625000000000 : ℚ) : ℝ) ≤ stT293 87 := by
  have hc : ((960421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64354929947/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((960421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c88 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-88283/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6631623/10000000) (δ := 14701/1000000000) (ψ := 1326617/1000000) 293 209
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t88 : ((-23530172793/250000000000 : ℚ) : ℝ) ≤ stT293 88 := by
  have hc : ((-88293/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23530172793/250000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-88293/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c89 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((791153/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1645261/10000000) (δ := 7351/500000000) (ψ := 1326617/1000000) 293 209
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t89 : ((838513806841/10000000000000 : ℚ) : ℝ) ≤ stT293 89 := by
  have hc : ((791053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((838513806841/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((791053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c90 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-17591/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -293913/500000) (δ := 14709/1000000000) (ψ := 1326617/1000000) 293 210
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t90 : ((-37090370391/500000000000 : ℚ) : ℝ) ≤ stT293 90 := by
  have hc : ((-35187/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37090370391/500000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-35187/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c91 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((632281/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 443151/2000000) (δ := 29309/1000000000) (ψ := 1326617/1000000) 293 210
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t91 : ((165676306851/2500000000000 : ℚ) : ℝ) ≤ stT293 91 := by
  have hc : ((632181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165676306851/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((632181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c92 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-116837/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5486679/10000000) (δ := 3679/250000000) (ψ := 1326617/1000000) 293 211
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t92 : ((-121831953061/2000000000000 : ℚ) : ℝ) ≤ stT293 92 := by
  have hc : ((-116857/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121831953061/2000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-116857/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c93 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((562887/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 486461/2000000) (δ := 14687/1000000000) (ψ := 1326617/1000000) 293 211
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t93 : ((583582542437/10000000000000 : ℚ) : ℝ) ≤ stT293 93 := by
  have hc : ((562787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((583582542437/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((562787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c94 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-284687/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5441351/10000000) (δ := 14679/1000000000) (ψ := 1326617/1000000) 293 212
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t94 : ((-146842003007/2500000000000 : ℚ) : ℝ) ≤ stT293 94 := by
  have hc : ((-284737/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146842003007/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-284737/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c95 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((602621/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2310037/10000000) (δ := 14779/1000000000) (ψ := 1326617/1000000) 293 212
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t95 : ((309086645269/5000000000000 : ℚ) : ℝ) ≤ stT293 95 := by
  have hc : ((602521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((309086645269/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((602521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c96 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-329799/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5727699/10000000) (δ := 3693/250000000) (ψ := 1326617/1000000) 293 213
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t96 : ((-336650816229/5000000000000 : ℚ) : ℝ) ≤ stT293 96 := by
  have hc : ((-329849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-336650816229/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-329849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c97 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((367469/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 465763/2500000) (δ := 3693/250000000) (ψ := 1326617/1000000) 293 213
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t97 : ((186528705987/2500000000000 : ℚ) : ℝ) ≤ stT293 97 := by
  have hc : ((367419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186528705987/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((367419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c98 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-164069/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -253281/400000) (δ := 2953/200000000) (ψ := 1326617/1000000) 293 214
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t98 : ((-165754995617/2000000000000 : ℚ) : ℝ) ≤ stT293 98 := by
  have hc : ((-164089/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165754995617/2000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-164089/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c99 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((180793/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 34519/312500) (δ := 2953/200000000) (ψ := 1326617/1000000) 293 214
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t99 : ((181683553601/2000000000000 : ℚ) : ℝ) ≤ stT293 99 := by
  have hc : ((180773/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181683553601/2000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((180773/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c100 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-48507/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -724151/1000000) (δ := 2949/200000000) (ψ := 1326617/1000000) 293 215
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t100 : ((-1516/15625 : ℚ) : ℝ) ≤ stT293 100 := by
  have hc : ((-3032/3125 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1516/15625 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-3032/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c101 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((499911/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23579/5000000) (δ := 2949/200000000) (ψ := 1326617/1000000) 293 215
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t101 : ((497380189857/5000000000000 : ℚ) : ℝ) ≤ stT293 101 := by
  have hc : ((499861/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((497380189857/5000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((499861/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c102 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-24307/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 226999/312500) (δ := 2969/200000000) (ψ := 1326617/1000000) 293 215
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t102 : ((-12035001403/125000000000 : ℚ) : ℝ) ≤ stT293 102 := by
  have hc : ((-48619/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12035001403/125000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-48619/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c103 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((173657/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1297653/10000000) (δ := 14851/1000000000) (ψ := 1326617/1000000) 293 216
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t103 : ((171089571573/2000000000000 : ℚ) : ℝ) ≤ stT293 103 := by
  have hc : ((173637/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171089571573/2000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((173637/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c104 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-135017/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5779689/10000000) (δ := 14751/1000000000) (ψ := 1326617/1000000) 293 216
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t104 : ((-132414716497/2000000000000 : ℚ) : ℝ) ≤ stT293 104 := by
  have hc : ((-135037/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132414716497/2000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-135037/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c105 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((196251/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -583723/2000000) (δ := 14759/1000000000) (ψ := 1326617/1000000) 293 217
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t105 : ((1914725559/50000000000 : ℚ) : ℝ) ≤ stT293 105 := by
  have hc : ((196201/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1914725559/50000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((196201/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c106 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-39007/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1006133/2500000) (δ := 3711/250000000) (ψ := 1326617/1000000) 293 217
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t106 : ((-18992040801/5000000000000 : ℚ) : ℝ) ≤ stT293 106 := by
  have hc : ((-39107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18992040801/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-39107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c107 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-344179/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2402701/5000000) (δ := 14767/1000000000) (ψ := 1326617/1000000) 293 218
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t107 : ((-332827247623/10000000000000 : ℚ) : ℝ) ≤ stT293 107 := by
  have hc : ((-344279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-332827247623/10000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-344279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c108 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((694233/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1004303/5000000) (δ := 14767/1000000000) (ψ := 1326617/1000000) 293 218
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t108 : ((2671717917/40000000000 : ℚ) : ℝ) ≤ stT293 108 := by
  have hc : ((694133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2671717917/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((694133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c109 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-935079/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3474099/5000000) (δ := 7337/500000000) (ψ := 1326617/1000000) 293 219
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t109 : ((-895739696033/10000000000000 : ℚ) : ℝ) ≤ stT293 109 := by
  have hc : ((-935179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-895739696033/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-935179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c110 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((994653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -129321/5000000) (δ := 14729/1000000000) (ψ := 1326617/1000000) 293 219
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t110 : ((474134246243/5000000000000 : ℚ) : ℝ) ≤ stT293 110 := by
  have hc : ((994553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((474134246243/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((994553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c111 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-207257/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 637041/1000000) (δ := 7337/500000000) (ψ := 1326617/1000000) 293 219
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t111 : ((-49185842139/625000000000 : ℚ) : ℝ) ≤ stT293 111 := by
  have hc : ((-103641/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49185842139/625000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-103641/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c112 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((111787/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1384027/5000000) (δ := 7361/500000000) (ψ := 1326617/1000000) 293 220
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t112 : ((52802571591/1250000000000 : ℚ) : ℝ) ≤ stT293 112 := by
  have hc : ((55881/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52802571591/1250000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((55881/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c113 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((36737/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3743139/10000000) (δ := 14781/1000000000) (ψ := 1326617/1000000) 293 220
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t113 : ((431402433/62500000000 : ℚ) : ℝ) ≤ stT293 113 := by
  have hc : ((36687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((431402433/62500000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((36687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c114 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-74009/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -275553/500000) (δ := 459/31250000) (ψ := 1326617/1000000) 293 221
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t114 : ((-69327500599/1250000000000 : ℚ) : ℝ) ≤ stT293 114 := by
  have hc : ((-148043/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69327500599/1250000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-148043/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c115 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((937803/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7091/80000) (δ := 2943/200000000) (ψ := 1326617/1000000) 293 221
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t115 : ((109301474789/1250000000000 : ℚ) : ℝ) ≤ stT293 115 := by
  have hc : ((937703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109301474789/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((937703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c116 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-968851/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 180709/250000) (δ := 2943/200000000) (ψ := 1326617/1000000) 293 221
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t116 : ((-899648717627/10000000000000 : ℚ) : ℝ) ≤ stT293 116 := by
  have hc : ((-968951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-899648717627/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-968951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c117 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((639623/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -219197/1000000) (δ := 1851/125000000) (ψ := 1326617/1000000) 293 222
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t117 : ((1182478027/20000000000 : ℚ) : ℝ) ≤ stT293 117 := by
  have hc : ((639523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1182478027/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((639523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c118 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-9207/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2021059/5000000) (δ := 3677/250000000) (ψ := 1326617/1000000) 293 222
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t118 : ((-339765821/80000000000 : ℚ) : ℝ) ≤ stT293 118 := by
  have hc : ((-9227/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-339765821/80000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-9227/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c119 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-145863/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -685553/1250000) (δ := 14703/1000000000) (ψ := 1326617/1000000) 293 223
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t119 : ((-4179230741/78125000000 : ℚ) : ℝ) ≤ stT293 119 := by
  have hc : ((-9118/15625 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4179230741/78125000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-9118/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c120 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((483433/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 161339/2500000) (δ := 14803/1000000000) (ψ := 1326617/1000000) 293 223
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t120 : ((44126583921/500000000000 : ℚ) : ℝ) ≤ stT293 120 := by
  have hc : ((483383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44126583921/500000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((483383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c121 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-449809/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6724227/10000000) (δ := 14803/1000000000) (ψ := 1326617/1000000) 293 223
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t121 : ((-408962768169/5000000000000 : ℚ) : ℝ) ≤ stT293 121 := by
  have hc : ((-449859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-408962768169/5000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-449859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c122 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((189557/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -590979/2000000) (δ := 1481/100000000) (ψ := 1326617/1000000) 293 224
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t122 : ((171571488999/5000000000000 : ℚ) : ℝ) ≤ stT293 122 := by
  have hc : ((189507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171571488999/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((189507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c123 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((353123/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1512361/5000000) (δ := 1471/100000000) (ψ := 1326617/1000000) 293 224
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t123 : ((318309895387/10000000000000 : ℚ) : ℝ) ≤ stT293 123 := by
  have hc : ((353023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((318309895387/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((353023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c124 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-904421/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3376021/5000000) (δ := 14817/1000000000) (ψ := 1326617/1000000) 293 225
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t124 : ((-812284280067/10000000000000 : ℚ) : ℝ) ≤ stT293 124 := by
  have hc : ((-904521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-812284280067/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-904521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c125 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((940267/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -108557/1250000) (δ := 7343/500000000) (ψ := 1326617/1000000) 293 225
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t125 : ((840910749309/10000000000000 : ℚ) : ℝ) ≤ stT293 125 := by
  have hc : ((940167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((840910749309/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((940167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c126 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-202283/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4968251/10000000) (δ := 14817/1000000000) (ψ := 1326617/1000000) 293 225
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t126 : ((-180252602043/5000000000000 : ℚ) : ℝ) ≤ stT293 126 := by
  have hc : ((-202333/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180252602043/5000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-202333/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c127 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-79519/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4949227/10000000) (δ := 14679/1000000000) (ψ := 1326617/1000000) 293 226
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t127 : ((-70579488423/2000000000000 : ℚ) : ℝ) ≤ stT293 127 := by
  have hc : ((-79539/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70579488423/2000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-79539/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c128 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((237437/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 795917/10000000) (δ := 14679/1000000000) (ψ := 1326617/1000000) 293 226
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t128 : ((52461107699/625000000000 : ℚ) : ℝ) ≤ stT293 128 := by
  have hc : ((59353/62500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52461107699/625000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((59353/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c129 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-856141/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6496379/10000000) (δ := 1853/125000000) (ψ := 1326617/1000000) 293 226
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t129 : ((-753878244691/10000000000000 : ℚ) : ℝ) ≤ stT293 129 := by
  have hc : ((-856241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-753878244691/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-856241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c130 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((148161/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -177761/500000) (δ := 3693/250000000) (ψ := 1326617/1000000) 293 227
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t130 : ((64929042269/5000000000000 : ℚ) : ℝ) ≤ stT293 130 := by
  have hc : ((148061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64929042269/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((148061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c131 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((679921/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 411571/2000000) (δ := 14831/1000000000) (ψ := 1326617/1000000) 293 227
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t131 : ((74245290873/1250000000000 : ℚ) : ℝ) ≤ stT293 131 := by
  have hc : ((679821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74245290873/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((679821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c132 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-39837/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119191/156250) (δ := 917/62500000) (ψ := 1326617/1000000) 293 227
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t132 : ((-34677168149/400000000000 : ℚ) : ℝ) ≤ stT293 132 := by
  have hc : ((-39841/40000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34677168149/400000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-39841/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c133 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((130721/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -510283/2000000) (δ := 7369/500000000) (ψ := 1326617/1000000) 293 228
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t133 : ((14165959733/312500000000 : ℚ) : ℝ) ≤ stT293 133 := by
  have hc : ((16337/31250 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14165959733/312500000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((16337/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c134 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((193143/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1467743/5000000) (δ := 14669/500000000) (ψ := 1326617/1000000) 293 228
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t134 : ((41701715931/1250000000000 : ℚ) : ℝ) ≤ stT293 134 := by
  have hc : ((193093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41701715931/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((193093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c135 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-977813/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -915797/1250000) (δ := 7423/500000000) (ψ := 1326617/1000000) 293 229
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t135 : ((-841653536319/10000000000000 : ℚ) : ℝ) ≤ stT293 135 := by
  have hc : ((-977913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-841653536319/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-977913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c136 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((89897/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1920453/10000000) (δ := 7373/500000000) (ψ := 1326617/1000000) 293 229
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t136 : ((38537619837/625000000000 : ℚ) : ℝ) ≤ stT293 136 := by
  have hc : ((179769/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38537619837/625000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((179769/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c137 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((38249/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 689183/2000000) (δ := 14657/1000000000) (ψ := 1326617/1000000) 293 229
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t137 : ((32661213753/2000000000000 : ℚ) : ℝ) ≤ stT293 137 := by
  have hc : ((38229/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32661213753/2000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((38229/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c138 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-466583/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1733699/2500000) (δ := 297/20000000) (ψ := 1326617/1000000) 293 230
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t138 : ((-397224607681/5000000000000 : ℚ) : ℝ) ≤ stT293 138 := by
  have hc : ((-466633/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-397224607681/5000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-466633/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c139 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((79099/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -822963/5000000) (δ := 59/4000000) (ψ := 1326617/1000000) 293 230
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t139 : ((16770585183/250000000000 : ℚ) : ℝ) ≤ stT293 139 := by
  have hc : ((79089/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16770585183/250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((79089/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c140 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((128441/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 721/2000) (δ := 297/20000000) (ψ := 1326617/1000000) 293 230
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t140 : ((54233954757/5000000000000 : ℚ) : ℝ) ≤ stT293 140 := by
  have hc : ((128341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54233954757/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((128341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c141 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-185299/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6889467/10000000) (δ := 369/25000000) (ψ := 1326617/1000000) 293 231
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t141 : ((-19508345811/250000000000 : ℚ) : ℝ) ≤ stT293 141 := by
  have hc : ((-185319/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19508345811/250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-185319/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c142 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((387179/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1712743/10000000) (δ := 369/25000000) (ψ := 1326617/1000000) 293 231
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t142 : ((324871301349/5000000000000 : ℚ) : ℝ) ≤ stT293 142 := by
  have hc : ((387129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((324871301349/5000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((387129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c143 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((198411/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3427649/10000000) (δ := 369/25000000) (ψ := 1326617/1000000) 293 231
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t143 : ((82917993631/5000000000000 : ℚ) : ℝ) ≤ stT293 143 := by
  have hc : ((198311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82917993631/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((198311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c144 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-120429/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1435163/2000000) (δ := 14667/1000000000) (ψ := 1326617/1000000) 293 232
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t144 : ((-100367996961/1250000000000 : ℚ) : ℝ) ≤ stT293 144 := by
  have hc : ((-240883/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100367996961/1250000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-240883/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c145 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((66551/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2106549/10000000) (δ := 921/62500000) (ψ := 1326617/1000000) 293 232
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t145 : ((27629619807/500000000000 : ℚ) : ℝ) ≤ stT293 145 := by
  have hc : ((66541/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27629619807/500000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((66541/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c146 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((194551/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58557/200000) (δ := 3709/250000000) (ψ := 1326617/1000000) 293 232
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t146 : ((32194000021/1000000000000 : ℚ) : ℝ) ≤ stT293 146 := by
  have hc : ((194501/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32194000021/1000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((194501/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c147 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-249891/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7780141/10000000) (δ := 7337/500000000) (ψ := 1326617/1000000) 293 233
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t147 : ((-51531866973/625000000000 : ℚ) : ℝ) ≤ stT293 147 := by
  have hc : ((-62479/62500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51531866973/625000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-62479/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c148 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((430631/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2814011/10000000) (δ := 14729/1000000000) (ψ := 1326617/1000000) 293 233
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t148 : ((176946949407/5000000000000 : ℚ) : ℝ) ≤ stT293 148 := by
  have hc : ((430531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176946949407/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((430531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c149 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((661869/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2118717/10000000) (δ := 14829/1000000000) (ψ := 1326617/1000000) 293 233
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t149 : ((542141679639/10000000000000 : ℚ) : ℝ) ≤ stT293 149 := by
  have hc : ((661769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((542141679639/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((661769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c150 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-472327/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7018337/10000000) (δ := 7387/500000000) (ψ := 1326617/1000000) 293 233
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t150 : ((-385694403369/5000000000000 : ℚ) : ℝ) ≤ stT293 150 := by
  have hc : ((-472377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-385694403369/5000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-472377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c151 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((41801/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3822457/10000000) (δ := 7341/500000000) (ψ := 1326617/1000000) 293 234
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t151 : ((8483943347/2500000000000 : ℚ) : ℝ) ≤ stT293 151 := by
  have hc : ((41701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8483943347/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((41701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c152 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((459547/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 253139/2500000) (δ := 7391/500000000) (ψ := 1326617/1000000) 293 234
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t152 : ((372701233179/5000000000000 : ℚ) : ℝ) ≤ stT293 152 := by
  have hc : ((459497/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((372701233179/5000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((459497/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c153 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-137137/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5815851/10000000) (δ := 14721/1000000000) (ψ := 1326617/1000000) 293 234
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t153 : ((-110884988121/2000000000000 : ℚ) : ℝ) ≤ stT293 153 := by
  have hc : ((-137157/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110884988121/2000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-137157/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c154 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-45933/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2560047/5000000) (δ := 14789/1000000000) (ψ := 1326617/1000000) 293 235
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t154 : ((-37021926089/1000000000000 : ℚ) : ℝ) ≤ stT293 154 := by
  have hc : ((-45943/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37021926089/1000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-45943/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c155 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((988531/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -94747/2500000) (δ := 14689/1000000000) (ψ := 1326617/1000000) 293 235
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t155 : ((793926559389/10000000000000 : ℚ) : ℝ) ≤ stT293 155 := by
  have hc : ((988431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((793926559389/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((988431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c156 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-40289/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2165823/5000000) (δ := 7357/500000000) (ψ := 1326617/1000000) 293 235
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t156 : ((-16138520637/1250000000000 : ℚ) : ℝ) ≤ stT293 156 := by
  have hc : ((-20157/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16138520637/1250000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-20157/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c157 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-894593/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6695789/10000000) (δ := 14807/1000000000) (ψ := 1326617/1000000) 293 236
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t157 : ((-714042852291/10000000000000 : ℚ) : ℝ) ≤ stT293 157 := by
  have hc : ((-894693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-714042852291/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-894693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c158 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((341841/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -409/2000) (δ := 14807/1000000000) (ψ := 1326617/1000000) 293 236
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t158 : ((271914222587/5000000000000 : ℚ) : ℝ) ≤ stT293 158 := by
  have hc : ((341791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((271914222587/5000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((341791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c159 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((128577/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2576489/10000000) (δ := 14807/1000000000) (ψ := 1326617/1000000) 293 236
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t159 : ((12743536519/312500000000 : ℚ) : ℝ) ≤ stT293 159 := by
  have hc : ((16069/31250 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12743536519/312500000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((16069/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c160 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-192539/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7168971/10000000) (δ := 14807/1000000000) (ψ := 1326617/1000000) 293 236
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t160 : ((-15223136863/200000000000 : ℚ) : ℝ) ≤ stT293 160 := by
  have hc : ((-192559/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15223136863/200000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-192559/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c161 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-19263/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3975151/10000000) (δ := 37/2500000) (ψ := 1326617/1000000) 293 237
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t161 : ((-15260193293/10000000000000 : ℚ) : ℝ) ≤ stT293 161 := by
  have hc : ((-19363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15260193293/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-19363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c162 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((974973/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 560489/10000000) (δ := 37/2500000) (ψ := 1326617/1000000) 293 237
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t162 : ((382966184701/5000000000000 : ℚ) : ℝ) ≤ stT293 162 := by
  have hc : ((974873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((382966184701/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((974873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c163 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-220401/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5068221/10000000) (δ := 147/10000000) (ψ := 1326617/1000000) 293 237
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t163 : ((-172670670711/5000000000000 : ℚ) : ℝ) ≤ stT293 163 := by
  have hc : ((-220451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172670670711/5000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-220451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c164 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-77899/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3079813/5000000) (δ := 14793/1000000000) (ψ := 1326617/1000000) 293 238
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t164 : ((-60836722921/1000000000000 : ℚ) : ℝ) ≤ stT293 164 := by
  have hc : ((-77909/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60836722921/1000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-77909/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c165 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((77587/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -853379/5000000) (δ := 1471/100000000) (ψ := 1326617/1000000) 293 238
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t165 : ((30196769673/500000000000 : ℚ) : ℝ) ≤ stT293 165 := by
  have hc : ((77577/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30196769673/500000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((77577/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c166 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((116133/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2719227/10000000) (δ := 1481/100000000) (ψ := 1326617/1000000) 293 238
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t166 : ((450586121/12500000000 : ℚ) : ℝ) ≤ stT293 166 := by
  have hc : ((29027/62500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((450586121/12500000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((29027/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c167 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-957059/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1423739/2000000) (δ := 1471/100000000) (ψ := 1326617/1000000) 293 238
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t167 : ((-11573009469/156250000000 : ℚ) : ℝ) ≤ stT293 167 := by
  have hc : ((-957159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11573009469/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-957159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c168 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-57707/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -421617/1000000) (δ := 14717/1000000000) (ψ := 1326617/1000000) 293 239
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t168 : ((-44560507369/5000000000000 : ℚ) : ℝ) ≤ stT293 168 := by
  have hc : ((-57757/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44560507369/5000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-57757/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c169 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((499313/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 131071/10000000) (δ := 14717/1000000000) (ψ := 1326617/1000000) 293 239
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t169 : ((38404807749/500000000000 : ℚ) : ℝ) ≤ stT293 169 := by
  have hc : ((499263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38404807749/500000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((499263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c170 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-208699/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4452601/10000000) (δ := 7343/500000000) (ψ := 1326617/1000000) 293 239
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t170 : ((-32028305007/2000000000000 : ℚ) : ℝ) ≤ stT293 170 := by
  have hc : ((-208799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32028305007/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-208799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c171 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-936627/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -869897/1250000) (δ := 593/40000000) (ψ := 1326617/1000000) 293 240
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t171 : ((-8954173393/125000000000 : ℚ) : ℝ) ≤ stT293 171 := by
  have hc : ((-936727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8954173393/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-936727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c172 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((237771/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1344021/5000000) (δ := 589/40000000) (ψ := 1326617/1000000) 293 240
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t172 : ((45315090183/1250000000000 : ℚ) : ℝ) ≤ stT293 172 := by
  have hc : ((237721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45315090183/1250000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((237721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c173 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((811937/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 779167/5000000) (δ := 593/40000000) (ψ := 1326617/1000000) 293 240
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t173 : ((123445498709/2000000000000 : ℚ) : ℝ) ≤ stT293 173 := by
  have hc : ((811837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123445498709/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((811837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c174 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-42203/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1445061/2500000) (δ := 589/40000000) (ψ := 1326617/1000000) 293 240
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t174 : ((-127995160863/2500000000000 : ℚ) : ℝ) ≤ stT293 174 := by
  have hc : ((-168837/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127995160863/2500000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-168837/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c175 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-165071/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2864991/5000000) (δ := 14771/1000000000) (ψ := 1326617/1000000) 293 241
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t175 : ((-15600106773/312500000000 : ℚ) : ℝ) ≤ stT293 175 := by
  have hc : ((-20637/31250 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15600106773/312500000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-20637/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c176 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((203109/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1556197/10000000) (δ := 14771/1000000000) (ψ := 1326617/1000000) 293 241
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t176 : ((19135031419/312500000000 : ℚ) : ℝ) ≤ stT293 176 := by
  have hc : ((50771/62500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19135031419/312500000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((50771/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c177 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((7942/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1297001/5000000) (δ := 3683/250000000) (ψ := 1326617/1000000) 293 241
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t177 : ((47747184681/1250000000000 : ℚ) : ℝ) ≤ stT293 177 := by
  have hc : ((127047/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47747184681/1250000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((127047/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c178 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-224753/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 168019/250000) (δ := 14771/1000000000) (ψ := 1326617/1000000) 293 241
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t178 : ((-21059787987/312500000000 : ℚ) : ℝ) ≤ stT293 178 := by
  have hc : ((-112389/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21059787987/312500000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-112389/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c179 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-11667/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2441759/5000000) (δ := 14739/1000000000) (ψ := 1326617/1000000) 293 242
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t179 : ((-17445343099/625000000000 : ℚ) : ℝ) ≤ stT293 179 := by
  have hc : ((-93361/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17445343099/625000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-93361/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c180 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((948887/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -802761/10000000) (δ := 3691/250000000) (ψ := 1326617/1000000) 293 242
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t180 : ((141436626877/2000000000000 : ℚ) : ℝ) ≤ stT293 180 := by
  have hc : ((948787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141436626877/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((948787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c181 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((265403/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 813859/2500000) (δ := 14739/1000000000) (ψ := 1326617/1000000) 293 242
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t181 : ((98599064041/5000000000000 : ℚ) : ℝ) ≤ stT293 181 := by
  have hc : ((265303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98599064041/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((265303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c182 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-974771/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3645609/5000000) (δ := 14739/1000000000) (ψ := 1326617/1000000) 293 242
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t182 : ((-578098503/8000000000 : ℚ) : ℝ) ≤ stT293 182 := by
  have hc : ((-974871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-578098503/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-974871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c183 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-9463/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1100753/2500000) (δ := 14757/1000000000) (ψ := 1326617/1000000) 293 243
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t183 : ((-874869237/62500000000 : ℚ) : ℝ) ≤ stT293 183 := by
  have hc : ((-2367/12500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-874869237/62500000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-2367/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c184 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((197301/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20559/500000) (δ := 14757/1000000000) (ψ := 1326617/1000000) 293 243
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t184 : ((145437328729/2000000000000 : ℚ) : ℝ) ≤ stT293 184 := by
  have hc : ((197281/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145437328729/2000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((197281/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c185 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((18331/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 889761/2500000) (δ := 7423/500000000) (ψ := 1326617/1000000) 293 243
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t185 : ((13468017659/1250000000000 : ℚ) : ℝ) ≤ stT293 185 := by
  have hc : ((36637/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13468017659/1250000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((36637/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c186 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-247607/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1501561/2000000) (δ := 7423/500000000) (ψ := 1326617/1000000) 293 243
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t186 : ((-2837073393/39062500000 : ℚ) : ℝ) ≤ stT293 186 := by
  have hc : ((-15477/15625 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2837073393/39062500000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-15477/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c187 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-68881/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2136247/5000000) (δ := 59/4000000) (ψ := 1326617/1000000) 293 244
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t187 : ((-50407379163/5000000000000 : ℚ) : ℝ) ≤ stT293 187 := by
  have hc : ((-68931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50407379163/5000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-68931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c188 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((989311/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -91463/2500000) (δ := 297/20000000) (ψ := 1326617/1000000) 293 244
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t188 : ((180363830841/2500000000000 : ℚ) : ℝ) ≤ stT293 188 := by
  have hc : ((989211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180363830841/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((989211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c189 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((6481/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1760067/5000000) (δ := 59/4000000) (ψ := 1326617/1000000) 293 244
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t189 : ((147228687/12500000000 : ℚ) : ℝ) ≤ stT293 189 := by
  have hc : ((6477/40000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147228687/12500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((6477/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c190 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-30703/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7385537/10000000) (δ := 14753/1000000000) (ψ := 1326617/1000000) 293 244
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t190 : ((-178212699573/2500000000000 : ℚ) : ℝ) ≤ stT293 190 := by
  have hc : ((-245649/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178212699573/2500000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-245649/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c191 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-218327/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4477241/10000000) (δ := 733/50000000) (ψ := 1326617/1000000) 293 245
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t191 : ((-6321932661/400000000000 : ℚ) : ℝ) ≤ stT293 191 := by
  have hc : ((-218427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6321932661/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-218427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c192 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((966163/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -652199/10000000) (δ := 369/25000000) (ψ := 1326617/1000000) 293 245
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t192 : ((697195108281/10000000000000 : ℚ) : ℝ) ≤ stT293 192 := by
  have hc : ((966063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((697195108281/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((966063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c193 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((304677/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98531/312500) (δ := 369/25000000) (ψ := 1326617/1000000) 293 245
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t193 : ((43847818651/2000000000000 : ℚ) : ℝ) ≤ stT293 193 := by
  have hc : ((304577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43847818651/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((304577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c194 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-186741/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 867319/1250000) (δ := 369/25000000) (ψ := 1326617/1000000) 293 245
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t194 : ((-134086740799/2000000000000 : ℚ) : ℝ) ≤ stT293 194 := by
  have hc : ((-186761/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134086740799/2000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-186761/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c195 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-5217/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -625417/1250000) (δ := 3667/250000000) (ψ := 1326617/1000000) 293 246
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t195 : ((-2989493679/100000000000 : ℚ) : ℝ) ≤ stT293 195 := by
  have hc : ((-20873/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2989493679/100000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-20873/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c196 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((109541/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -50261/400000) (δ := 923/62500000) (ψ := 1326617/1000000) 293 246
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t196 : ((31293825849/500000000000 : ℚ) : ℝ) ≤ stT293 196 := by
  have hc : ((219057/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31293825849/500000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((219057/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c197 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((549947/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61781/250000) (δ := 2967/200000000) (ψ := 1326617/1000000) 293 246
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t197 : ((39174949209/1000000000000 : ℚ) : ℝ) ≤ stT293 197 := by
  have hc : ((549847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39174949209/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((549847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c198 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-784101/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1545027/2500000) (δ := 923/62500000) (ψ := 1326617/1000000) 293 246
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t198 : ((-55730812467/1000000000000 : ℚ) : ℝ) ≤ stT293 198 := by
  have hc : ((-784201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55730812467/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-784201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c199 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-692011/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5837667/10000000) (δ := 587/40000000) (ψ := 1326617/1000000) 293 247
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t199 : ((-245312514951/5000000000000 : ℚ) : ℝ) ≤ stT293 199 := by
  have hc : ((-692111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245312514951/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-692111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c200 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((647571/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2166011/10000000) (δ := 1841/125000000) (ψ := 1326617/1000000) 293 247
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t200 : ((228915314463/5000000000000 : ℚ) : ℝ) ≤ stT293 200 := by
  have hc : ((647471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228915314463/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((647471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c201 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((82817/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 743703/5000000) (δ := 1841/125000000) (ψ := 1326617/1000000) 293 247
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t201 : ((11681500683/200000000000 : ℚ) : ℝ) ≤ stT293 201 := by
  have hc : ((82807/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11681500683/200000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((82807/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c202 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-92043/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 640323/1250000) (δ := 587/40000000) (ψ := 1326617/1000000) 293 247
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t202 : ((-32387671337/1000000000000 : ℚ) : ℝ) ≤ stT293 202 := by
  have hc : ((-92063/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32387671337/1000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-92063/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c203 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-234467/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -278723/400000) (δ := 14821/1000000000) (ψ := 1326617/1000000) 293 248
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t203 : ((-41145314649/625000000000 : ℚ) : ℝ) ≤ stT293 203 := by
  have hc : ((-58623/62500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41145314649/625000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-58623/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c204 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((55379/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -336857/1000000) (δ := 14821/1000000000) (ψ := 1326617/1000000) 293 248
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t204 : ((968888739/62500000000 : ℚ) : ℝ) ≤ stT293 204 := by
  have hc : ((27677/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((968888739/62500000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((27677/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c205 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((996361/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42671/2000000) (δ := 14821/1000000000) (ψ := 1326617/1000000) 293 248
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t205 : ((69581857023/1000000000000 : ℚ) : ℝ) ≤ stT293 205 := by
  have hc : ((996261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69581857023/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((996261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c206 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((29811/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3777847/10000000) (δ := 7341/500000000) (ψ := 1326617/1000000) 293 248
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t206 : ((20735470813/5000000000000 : ℚ) : ℝ) ≤ stT293 206 := by
  have hc : ((29761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20735470813/5000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((29761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c207 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-488851/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7325051/10000000) (δ := 14821/1000000000) (ψ := 1326617/1000000) 293 248
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t207 : ((-339810151149/5000000000000 : ℚ) : ℝ) ≤ stT293 207 := by
  have hc : ((-488901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-339810151149/5000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-488901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c208 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-90477/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -194111/400000) (δ := 7407/500000000) (ψ := 1326617/1000000) 293 249
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t208 : ((-245124667/9765625000 : ℚ) : ℝ) ≤ stT293 208 := by
  have hc : ((-45251/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245124667/9765625000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-45251/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c209 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((859849/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -669779/5000000) (δ := 14689/1000000000) (ψ := 1326617/1000000) 293 249
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t209 : ((297350209893/5000000000000 : ℚ) : ℝ) ≤ stT293 209 := by
  have hc : ((859749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((297350209893/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((859749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c210 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((162587/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 539221/2500000) (δ := 7357/500000000) (ψ := 1326617/1000000) 293 249
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t210 : ((11217834653/250000000000 : ℚ) : ℝ) ≤ stT293 210 := by
  have hc : ((81281/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11217834653/250000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((81281/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c211 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-9872/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5636699/10000000) (δ := 14789/1000000000) (ψ := 1326617/1000000) 293 249
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t211 : ((-108755948133/2500000000000 : ℚ) : ℝ) ≤ stT293 211 := by
  have hc : ((-157977/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108755948133/2500000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-157977/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c212 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-878339/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6607931/10000000) (δ := 3699/250000000) (ψ := 1326617/1000000) 293 250
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t212 : ((-603314540517/10000000000000 : ℚ) : ℝ) ≤ stT293 212 := by
  have hc : ((-878439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-603314540517/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-878439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c213 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((150839/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -158043/500000) (δ := 14807/1000000000) (ψ := 1326617/1000000) 293 250
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t213 : ((25829703333/1250000000000 : ℚ) : ℝ) ≤ stT293 213 := by
  have hc : ((150789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25829703333/1250000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((150789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c214 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((994169/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 270097/10000000) (δ := 14707/1000000000) (ψ := 1326617/1000000) 293 250
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t214 : ((135906131473/2000000000000 : ℚ) : ℝ) ≤ stT293 214 := by
  have hc : ((994069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135906131473/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((994069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c215 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((302/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 921253/2500000) (δ := 14707/1000000000) (ψ := 1326617/1000000) 293 250
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t215 : ((1645992519/250000000000 : ℚ) : ℝ) ≤ stT293 215 := by
  have hc : ((4827/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1645992519/250000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((4827/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c216 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-952957/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1416821/2000000) (δ := 14707/1000000000) (ψ := 1326617/1000000) 293 250
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t216 : ((-324236662799/5000000000000 : ℚ) : ℝ) ≤ stT293 216 := by
  have hc : ((-953057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324236662799/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-953057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c217 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-501567/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2620257/5000000) (δ := 14699/1000000000) (ψ := 1326617/1000000) 293 251
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t217 : ((-68110826923/2000000000000 : ℚ) : ℝ) ≤ stT293 217 := by
  have hc : ((-501667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68110826923/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-501667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c218 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((183079/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1872699/10000000) (δ := 14799/1000000000) (ψ := 1326617/1000000) 293 251
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t218 : ((12397972839/250000000000 : ℚ) : ℝ) ≤ stT293 218 := by
  have hc : ((91527/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12397972839/250000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((91527/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c219 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((414943/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 739867/5000000) (δ := 14699/1000000000) (ψ := 1326617/1000000) 293 251
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t219 : ((280358551141/5000000000000 : ℚ) : ℝ) ≤ stT293 219 := by
  have hc : ((414893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((280358551141/5000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((414893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c220 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-174239/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2408429/5000000) (δ := 3701/250000000) (ψ := 1326617/1000000) 293 251
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t220 : ((-587528219/25000000000 : ℚ) : ℝ) ≤ stT293 220 := by
  have hc : ((-174289/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-587528219/25000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-174289/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c221 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-993513/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -473067/625000) (δ := 1849/125000000) (ψ := 1326617/1000000) 293 252
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t221 : ((-668376637549/10000000000000 : ℚ) : ℝ) ≤ stT293 221 := by
  have hc : ((-993613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-668376637549/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-993613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c222 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-133653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4262127/10000000) (δ := 14711/1000000000) (ψ := 1326617/1000000) 293 252
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t222 : ((-89769262221/10000000000000 : ℚ) : ℝ) ≤ stT293 222 := by
  have hc : ((-133753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89769262221/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-133753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c223 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((925671/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -969979/10000000) (δ := 14711/1000000000) (ψ := 1326617/1000000) 293 252
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t223 : ((619807694579/10000000000000 : ℚ) : ℝ) ≤ stT293 223 := by
  have hc : ((925571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((619807694579/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((925571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c224 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((75431/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1153723/5000000) (δ := 14811/1000000000) (ψ := 1326617/1000000) 293 252
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t224 : ((100782194061/2500000000000 : ℚ) : ℝ) ≤ stT293 224 := by
  have hc : ((150837/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100782194061/2500000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((150837/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c225 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-305499/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2785147/5000000) (δ := 14811/1000000000) (ψ := 1326617/1000000) 293 252
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t225 : ((-203699435183/5000000000000 : ℚ) : ℝ) ≤ stT293 225 := by
  have hc : ((-305549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203699435183/5000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-305549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c226 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-11581/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3444681/5000000) (δ := 5877/200000000) (ψ := 1326617/1000000) 293 253
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t226 : ((-30817633839/500000000000 : ℚ) : ℝ) ≤ stT293 226 := by
  have hc : ((-46329/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30817633839/500000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-46329/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c227 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((108447/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1827669/5000000) (δ := 2957/200000000) (ψ := 1326617/1000000) 293 253
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t227 : ((71912395881/10000000000000 : ℚ) : ℝ) ≤ stT293 227 := by
  have hc : ((108347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71912395881/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((108347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c228 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((984861/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -435561/10000000) (δ := 2957/200000000) (ψ := 1326617/1000000) 293 253
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t228 : ((326086864213/5000000000000 : ℚ) : ℝ) ≤ stT293 228 := by
  have hc : ((984761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((326086864213/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((984761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c229 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((223199/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 346269/1250000) (δ := 2957/200000000) (ψ := 1326617/1000000) 293 253
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t229 : ((73730437941/2500000000000 : ℚ) : ℝ) ≤ stT293 229 := by
  have hc : ((223149/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73730437941/2500000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((223149/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c230 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-22719/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9539/16000) (δ := 7409/500000000) (ψ := 1326617/1000000) 293 253
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t230 : ((-119860300037/2500000000000 : ℚ) : ℝ) ≤ stT293 230 := by
  have hc : ((-181777/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119860300037/2500000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-181777/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c231 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-870633/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6568211/10000000) (δ := 7389/500000000) (ψ := 1326617/1000000) 293 254
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t231 : ((-17903141213/312500000000 : ℚ) : ℝ) ≤ stT293 231 := by
  have hc : ((-870733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17903141213/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-870733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c232 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((207633/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -425513/1250000) (δ := 7389/500000000) (ψ := 1326617/1000000) 293 254
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t232 : ((34063013889/2500000000000 : ℚ) : ℝ) ≤ stT293 232 := by
  have hc : ((207533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34063013889/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((207533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c233 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((994861/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63387/2500000) (δ := 7339/500000000) (ψ := 1326617/1000000) 293 254
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t233 : ((651688821081/10000000000000 : ℚ) : ℝ) ≤ stT293 233 := by
  have hc : ((994761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((651688821081/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((994761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c234 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((405371/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 288353/1000000) (δ := 589/40000000) (ψ := 1326617/1000000) 293 254
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t234 : ((6623343953/250000000000 : ℚ) : ℝ) ≤ stT293 234 := by
  have hc : ((405271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6623343953/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((405271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c235 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-739337/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6007203/10000000) (δ := 589/40000000) (ψ := 1326617/1000000) 293 254
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t235 : ((-482356198773/10000000000000 : ℚ) : ℝ) ≤ stT293 235 := by
  have hc : ((-739437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-482356198773/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-739437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c236 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-174991/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3295173/5000000) (δ := 14771/1000000000) (ψ := 1326617/1000000) 293 255
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t236 : ((-22784507079/400000000000 : ℚ) : ℝ) ≤ stT293 236 := by
  have hc : ((-175011/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22784507079/400000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-175011/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c237 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((4317/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -873279/2500000) (δ := 14671/1000000000) (ψ := 1326617/1000000) 293 255
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t237 : ((5605130901/500000000000 : ℚ) : ℝ) ≤ stT293 237 := by
  have hc : ((8629/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5605130901/500000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((8629/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c238 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((246663/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16357/400000) (δ := 14771/1000000000) (ψ := 1326617/1000000) 293 255
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t238 : ((79935745757/1250000000000 : ℚ) : ℝ) ≤ stT293 238 := by
  have hc : ((123319/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79935745757/1250000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((123319/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c239 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((121137/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21299/80000) (δ := 927/62500000) (ψ := 1326617/1000000) 293 255
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t239 : ((4896300797/156250000000 : ℚ) : ℝ) ≤ stT293 239 := by
  have hc : ((15139/31250 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4896300797/156250000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((15139/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c240 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-328769/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1144171/2000000) (δ := 14671/1000000000) (ψ := 1326617/1000000) 293 255
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t240 : ((-106126003431/2500000000000 : ℚ) : ℝ) ≤ stT293 240 := by
  have hc : ((-328819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106126003431/2500000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-328819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c241 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-233527/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6941373/10000000) (δ := 14739/1000000000) (ψ := 1326617/1000000) 293 256
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t241 : ((-9402759729/156250000000 : ℚ) : ℝ) ≤ stT293 241 := by
  have hc : ((-14597/15625 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9402759729/156250000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-14597/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c242 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((7501/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3908237/10000000) (δ := 14739/1000000000) (ψ := 1326617/1000000) 293 256
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t242 : ((594692553/1250000000000 : ℚ) : ℝ) ≤ stT293 242 := by
  have hc : ((7401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((594692553/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((7401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c243 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((937629/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -887627/10000000) (δ := 1833/125000000) (ψ := 1326617/1000000) 293 256
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t243 : ((1202849707/20000000000 : ℚ) : ℝ) ≤ stT293 243 := by
  have hc : ((937529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1202849707/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((937529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c244 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((661303/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 530151/2500000) (δ := 1833/125000000) (ψ := 1326617/1000000) 293 256
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t244 : ((52911447669/1250000000000 : ℚ) : ℝ) ≤ stT293 244 := by
  have hc : ((661203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52911447669/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((661203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c245 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-9161/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1279123/2500000) (δ := 3683/125000000) (ψ := 1326617/1000000) 293 256
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t245 : ((-5854029951/200000000000 : ℚ) : ℝ) ≤ stT293 245 := by
  have hc : ((-9163/20000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5854029951/200000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-9163/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c246 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-995153/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3803871/5000000) (δ := 229/15625000) (ψ := 1326617/1000000) 293 257
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t246 : ((-634550421981/10000000000000 : ℚ) : ℝ) ≤ stT293 246 := by
  have hc : ((-995253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-634550421981/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-995253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c247 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-279869/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -579517/1250000) (δ := 229/15625000) (ψ := 1326617/1000000) 293 257
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t247 : ((-35628015033/2000000000000 : ℚ) : ℝ) ≤ stT293 247 := by
  have hc : ((-279969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35628015033/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-279969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c248 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((391719/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1676543/10000000) (δ := 229/15625000) (ψ := 1326617/1000000) 293 257
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t248 : ((49741963/1000000000 : ℚ) : ℝ) ≤ stT293 248 := by
  have hc : ((391669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49741963/1000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((391669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c249 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((873503/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 127111/1000000) (δ := 3689/250000000) (ψ := 1326617/1000000) 293 257
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t249 : ((138374110693/2500000000000 : ℚ) : ℝ) ≤ stT293 249 := by
  have hc : ((873403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138374110693/2500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((873403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c250 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-111787/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1051761/2500000) (δ := 14847/1000000000) (ψ := 1326617/1000000) 293 257
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t250 : ((-8845450559/1250000000000 : ℚ) : ℝ) ≤ stT293 250 := by
  have hc : ((-111887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8845450559/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-111887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c251 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-191699/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 445699/625000) (δ := 14847/1000000000) (ψ := 1326617/1000000) 293 257
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t251 : ((-24202414841/400000000000 : ℚ) : ℝ) ≤ stT293 251 := by
  have hc : ((-191719/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).2
  have h0 : (0:ℝ) ≤ ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24202414841/400000000000 : ℚ) : ℝ)
      = ((126239/2000000 : ℚ) : ℝ) * ((-191719/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c252 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-640323/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5664287/10000000) (δ := 14849/1000000000) (ψ := 1326617/1000000) 293 258
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t252 : ((-403428705043/10000000000000 : ℚ) : ℝ) ≤ stT293 252 := by
  have hc : ((-640423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-403428705043/10000000000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-640423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c253 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((448851/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1381647/5000000) (δ := 14849/1000000000) (ψ := 1326617/1000000) 293 258
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t253 : ((141063530597/5000000000000 : ℚ) : ℝ) ≤ stT293 253 := by
  have hc : ((448751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).1
  have hw2 : ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((314347/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141063530597/5000000000000 : ℚ) : ℝ)
      = ((314347/5000000 : ℚ) : ℝ) * ((448751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c254 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((39949/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1973/156250) (δ := 14849/1000000000) (ψ := 1326617/1000000) 293 258
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t254 : ((1002547599/16000000000 : ℚ) : ℝ) ≤ stT293 254 := by
  have hc : ((7989/8000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).1
  have hw2 : ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((125491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1002547599/16000000000 : ℚ) : ℝ)
      = ((125491/2000000 : ℚ) : ℝ) * ((7989/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c255 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((72137/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 600897/2000000) (δ := 7377/500000000) (ψ := 1326617/1000000) 293 258
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t255 : ((2822587263/125000000000 : ℚ) : ℝ) ≤ stT293 255 := by
  have hc : ((72117/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).1
  have hw2 : ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39139/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2822587263/125000000000 : ℚ) : ℝ)
      = ((39139/625000 : ℚ) : ℝ) * ((72117/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c256 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-175423/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 733927/1250000) (δ := 14849/1000000000) (ψ := 1326617/1000000) 293 258
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t256 : ((-13706896931/312500000000 : ℚ) : ℝ) ≤ stT293 256 := by
  have hc : ((-21931/31250 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).2
  have h0 : (0:ℝ) ≤ ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13706896931/312500000000 : ℚ) : ℝ)
      = ((625001/10000000 : ℚ) : ℝ) * ((-21931/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c257 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-7517/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3490411/5000000) (δ := 14761/1000000000) (ψ := 1326617/1000000) 293 259
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t257 : ((-23447379187/400000000000 : ℚ) : ℝ) ≤ stT293 257 := by
  have hc : ((-37589/40000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).2
  have h0 : (0:ℝ) ≤ ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23447379187/400000000000 : ℚ) : ℝ)
      = ((623783/10000000 : ℚ) : ℝ) * ((-37589/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c258 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-8357/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4136159/10000000) (δ := 7421/500000000) (ψ := 1326617/1000000) 293 259
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t258 : ((-5209068291/1000000000000 : ℚ) : ℝ) ≤ stT293 258 := by
  have hc : ((-8367/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).2
  have h0 : (0:ℝ) ≤ ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5209068291/1000000000000 : ℚ) : ℝ)
      = ((622573/10000000 : ℚ) : ℝ) * ((-8367/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c259 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((34693/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -651241/5000000) (δ := 14761/1000000000) (ψ := 1326617/1000000) 293 259
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t259 : ((21554669241/400000000000 : ℚ) : ℝ) ≤ stT293 259 := by
  have hc : ((34689/40000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).1
  have hw2 : ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((621369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21554669241/400000000000 : ℚ) : ℝ)
      = ((621369/10000000 : ℚ) : ℝ) * ((34689/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c260 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((102591/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38007/250000) (δ := 14761/1000000000) (ψ := 1326617/1000000) 293 259
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t260 : ((127232832161/2500000000000 : ℚ) : ℝ) ≤ stT293 260 := by
  have hc : ((205157/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).1
  have hw2 : ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((620173/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127232832161/2500000000000 : ℚ) : ℝ)
      = ((620173/10000000 : ℚ) : ℝ) * ((205157/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c261 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-1291/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4332201/10000000) (δ := 14761/1000000000) (ψ := 1326617/1000000) 293 259
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t261 : ((-799604823/80000000000 : ℚ) : ℝ) ≤ stT293 261 := by
  have hc : ((-6459/40000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-799604823/80000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-6459/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c262 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-958743/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3566677/5000000) (δ := 43961/1000000000) (ψ := 1326617/1000000) 293 259
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t262 : ((-592376081929/10000000000000 : ℚ) : ℝ) ≤ stT293 262 := by
  have hc : ((-958843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-592376081929/10000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-958843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c263 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-1691/2500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5784151/10000000) (δ := 2967/200000000) (ψ := 1326617/1000000) 293 260
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t263 : ((-834296331/20000000000 : ℚ) : ℝ) ≤ stT293 263 := by
  have hc : ((-1353/2000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).2
  have h0 : (0:ℝ) ≤ ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-834296331/20000000000 : ℚ) : ℝ)
      = ((616627/10000000 : ℚ) : ℝ) * ((-1353/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c264 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((45097/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37553/125000) (δ := 8807/200000000) (ψ := 1326617/1000000) 293 260
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t264 : ((55495142233/2500000000000 : ℚ) : ℝ) ≤ stT293 264 := by
  have hc : ((90169/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55495142233/2500000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((90169/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c265 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((99559/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -234877/10000000) (δ := 3667/250000000) (ψ := 1326617/1000000) 293 260
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t265 : ((12230490591/200000000000 : ℚ) : ℝ) ≤ stT293 265 := by
  have hc : ((99549/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12230490591/200000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((99549/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c266 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((532171/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 631021/2500000) (δ := 2947/200000000) (ψ := 1326617/1000000) 293 260
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t266 : ((326233480869/10000000000000 : ℚ) : ℝ) ≤ stT293 266 := by
  have hc : ((532071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).1
  have hw2 : ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((613139/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((326233480869/10000000000000 : ℚ) : ℝ)
      = ((613139/10000000 : ℚ) : ℝ) * ((532071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c267 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-128161/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1318161/2500000) (δ := 3667/250000000) (ψ := 1326617/1000000) 293 260
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t267 : ((-39224339163/1250000000000 : ℚ) : ℝ) ≤ stT293 267 := by
  have hc : ((-64093/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39224339163/1250000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-64093/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c268 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-99803/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1539403/2000000) (δ := 3707/250000000) (ψ := 1326617/1000000) 293 261
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t268 : ((-1905330357/31250000000 : ℚ) : ℝ) ≤ stT293 268 := by
  have hc : ((-99813/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1905330357/31250000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-99813/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c269 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-253/625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1242223/2500000) (δ := 3707/250000000) (ψ := 1326617/1000000) 293 261
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t269 : ((-2468719839/100000000000 : ℚ) : ℝ) ≤ stT293 269 := by
  have hc : ((-4049/10000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).2
  have h0 : (0:ℝ) ≤ ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2468719839/100000000000 : ℚ) : ℝ)
      = ((609711/10000000 : ℚ) : ℝ) * ((-4049/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c270 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((124267/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2250877/10000000) (δ := 587/40000000) (ψ := 1326617/1000000) 293 261
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t270 : ((3780711963/100000000000 : ℚ) : ℝ) ≤ stT293 270 := by
  have hc : ((124247/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3780711963/100000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((124247/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c271 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((983331/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 228551/5000000) (δ := 1841/125000000) (ψ := 1326617/1000000) 293 261
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t271 : ((18664674073/312500000000 : ℚ) : ℝ) ≤ stT293 271 := by
  have hc : ((983231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18664674073/312500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((983231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c272 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((60779/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1577523/5000000) (δ := 1841/125000000) (ψ := 1326617/1000000) 293 261
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t272 : ((36840551301/2000000000000 : ℚ) : ℝ) ≤ stT293 272 := by
  have hc : ((60759/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36840551301/2000000000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((60759/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c273 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-346789/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5843101/10000000) (δ := 3707/250000000) (ψ := 1326617/1000000) 293 261
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t273 : ((-52479168573/1250000000000 : ℚ) : ℝ) ≤ stT293 273 := by
  have hc : ((-346839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52479168573/1250000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-346839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c274 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-482287/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7186549/10000000) (δ := 23/1562500) (ψ := 1326617/1000000) 293 262
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t274 : ((-291390875451/5000000000000 : ℚ) : ℝ) ≤ stT293 274 := by
  have hc : ((-482337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291390875451/5000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-482337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c275 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-14641/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7229/16000) (δ := 741/50000000) (ψ := 1326617/1000000) 293 262
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t275 : ((-35330514547/2500000000000 : ℚ) : ℝ) ≤ stT293 275 := by
  have hc : ((-58589/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35330514547/2500000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-58589/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c276 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((183989/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58103/312500) (δ := 14683/1000000000) (ψ := 1326617/1000000) 293 262
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t276 : ((27683316639/625000000000 : ℚ) : ℝ) ≤ stT293 276 := by
  have hc : ((45991/62500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27683316639/625000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((45991/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c277 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((475247/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 789937/10000000) (δ := 14783/1000000000) (ψ := 1326617/1000000) 293 262
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t277 : ((285517840677/5000000000000 : ℚ) : ℝ) ≤ stT293 277 := by
  have hc : ((475197/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((285517840677/5000000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((475197/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c278 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((197657/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1714787/5000000) (δ := 14783/1000000000) (ψ := 1326617/1000000) 293 262
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t278 : ((1481084829/125000000000 : ℚ) : ℝ) ≤ stT293 278 := by
  have hc : ((197557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1481084829/125000000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((197557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c279 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-753309/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 757461/1250000) (δ := 23/1562500) (ψ := 1326617/1000000) 293 262
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t279 : ((-90210933433/2000000000000 : ℚ) : ℝ) ≤ stT293 279 := by
  have hc : ((-753409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90210933433/2000000000000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-753409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c280 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-189169/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7027463/10000000) (δ := 1479/100000000) (ψ := 1326617/1000000) 293 263
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t280 : ((-22612436847/400000000000 : ℚ) : ℝ) ≤ stT293 280 := by
  have hc : ((-189189/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22612436847/400000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-189189/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c281 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-97199/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4416101/10000000) (δ := 14713/1000000000) (ψ := 1326617/1000000) 293 263
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t281 : ((-1160277819/100000000000 : ℚ) : ℝ) ≤ stT293 281 := by
  have hc : ((-97249/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1160277819/100000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-97249/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c282 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((74811/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -113373/625000) (δ := 14713/1000000000) (ψ := 1326617/1000000) 293 263
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t282 : ((44543322291/1000000000000 : ℚ) : ℝ) ≤ stT293 282 := by
  have hc : ((74801/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44543322291/1000000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((74801/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c283 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((237963/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97367/1250000) (δ := 1479/100000000) (ψ := 1326617/1000000) 293 263
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t283 : ((35359847211/625000000000 : ℚ) : ℝ) ≤ stT293 283 := by
  have hc : ((118969/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35359847211/625000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((118969/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c284 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((223783/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 840689/2500000) (δ := 14713/1000000000) (ψ := 1326617/1000000) 293 263
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t284 : ((13273125537/1000000000000 : ℚ) : ℝ) ≤ stT293 284 := by
  have hc : ((223683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13273125537/1000000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((223683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c285 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-11254/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 296871/500000) (δ := 14813/1000000000) (ψ := 1326617/1000000) 293 263
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t285 : ((-106675539061/2500000000000 : ℚ) : ℝ) ≤ stT293 285 := by
  have hc : ((-180089/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106675539061/2500000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-180089/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c286 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-241619/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1440963/2000000) (δ := 14697/1000000000) (ψ := 1326617/1000000) 293 264
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t286 : ((-35721809643/625000000000 : ℚ) : ℝ) ≤ stT293 286 := by
  have hc : ((-60411/62500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35721809643/625000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-60411/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c287 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-284459/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4648097/10000000) (δ := 14697/1000000000) (ψ := 1326617/1000000) 293 264
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t287 : ((-83985027819/5000000000000 : ℚ) : ℝ) ≤ stT293 287 := by
  have hc : ((-284559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83985027819/5000000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-284559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c288 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((667369/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -525079/2500000) (δ := 7403/500000000) (ψ := 1326617/1000000) 293 264
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t288 : ((78638318919/2000000000000 : ℚ) : ℝ) ≤ stT293 288 := by
  have hc : ((667269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78638318919/2000000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((667269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c289 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((196929/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109669/2500000) (δ := 14697/1000000000) (ψ := 1326617/1000000) 293 264
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t289 : ((23165753123/400000000000 : ℚ) : ℝ) ≤ stT293 289 := by
  have hc : ((196909/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23165753123/400000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((196909/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c290 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((74781/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2968951/10000000) (δ := 14797/1000000000) (ψ := 1326617/1000000) 293 264
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t290 : ((2195057721/100000000000 : ℚ) : ℝ) ≤ stT293 290 := by
  have hc : ((74761/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2195057721/100000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((74761/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c291 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-146351/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1098087/2000000) (δ := 7403/500000000) (ψ := 1326617/1000000) 293 264
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t291 : ((-10725902667/312500000000 : ℚ) : ℝ) ≤ stT293 291 := by
  have hc : ((-18297/31250 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).2
  have h0 : (0:ℝ) ≤ ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10725902667/312500000000 : ℚ) : ℝ)
      = ((586211/10000000 : ℚ) : ℝ) * ((-18297/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c292 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-124777/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7704613/10000000) (δ := 3701/250000000) (ψ := 1326617/1000000) 293 265
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t292 : ((-73027564137/1250000000000 : ℚ) : ℝ) ≤ stT293 292 := by
  have hc : ((-249579/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73027564137/1250000000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-249579/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c293 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-243801/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2600171/5000000) (δ := 3701/250000000) (ψ := 1326617/1000000) 293 265
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t293 : ((-142459461157/5000000000000 : ℚ) : ℝ) ≤ stT293 293 := by
  have hc : ((-243851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142459461157/5000000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-243851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c294 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((46969/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1352321/5000000) (δ := 14799/1000000000) (ψ := 1326617/1000000) 293 265
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t294 : ((27387005349/1000000000000 : ℚ) : ℝ) ≤ stT293 294 := by
  have hc : ((46959/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).1
  have hw2 : ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((583211/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27387005349/1000000000000 : ℚ) : ℝ)
      = ((583211/10000000 : ℚ) : ℝ) * ((46959/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c295 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((996223/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43473/2000000) (δ := 14799/1000000000) (ψ := 1326617/1000000) 293 265
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t295 : ((289982362653/5000000000000 : ℚ) : ℝ) ≤ stT293 295 := by
  have hc : ((996123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).1
  have hw2 : ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((291111/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((289982362653/5000000000000 : ℚ) : ℝ)
      = ((291111/5000000 : ℚ) : ℝ) * ((996123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c296 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((154501/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2261489/10000000) (δ := 3701/250000000) (ψ := 1326617/1000000) 293 265
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t296 : ((11223415161/312500000000 : ℚ) : ℝ) ≤ stT293 296 := by
  have hc : ((38619/62500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).1
  have hw2 : ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11223415161/312500000000 : ℚ) : ℝ)
      = ((290619/5000000 : ℚ) : ℝ) * ((38619/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c297 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-19779/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4731991/10000000) (δ := 14799/1000000000) (ψ := 1326617/1000000) 293 265
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t297 : ((-45922277519/2500000000000 : ℚ) : ℝ) ≤ stT293 297 := by
  have hc : ((-79141/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45922277519/2500000000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-79141/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c298 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-965371/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 224817/312500) (δ := 3701/250000000) (ψ := 1326617/1000000) 293 265
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t298 : ((-111856573647/2000000000000 : ℚ) : ℝ) ≤ stT293 298 := by
  have hc : ((-965471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).2
  have h0 : (0:ℝ) ≤ ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111856573647/2000000000000 : ℚ) : ℝ)
      = ((115857/2000000 : ℚ) : ℝ) * ((-965471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c299 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-753357/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6059871/10000000) (δ := 14811/1000000000) (ψ := 1326617/1000000) 293 266
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t299 : ((-87147096991/2000000000000 : ℚ) : ℝ) ≤ stT293 299 := by
  have hc : ((-753457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).2
  have h0 : (0:ℝ) ≤ ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87147096991/2000000000000 : ℚ) : ℝ)
      = ((115663/2000000 : ℚ) : ℝ) * ((-753457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c300 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((124819/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3614127/10000000) (δ := 14711/1000000000) (ψ := 1326617/1000000) 293 266
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t300 : ((1440130293/200000000000 : ℚ) : ℝ) ≤ stT293 300 := by
  have hc : ((124719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1440130293/200000000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((124719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c301 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((445647/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -588257/5000000) (δ := 1849/125000000) (ψ := 1326617/1000000) 293 266
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t301 : ((25683765483/500000000000 : ℚ) : ℝ) ≤ stT293 301 := by
  have hc : ((445597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25683765483/500000000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((445597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c302 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((876999/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 626521/5000000) (δ := 1849/125000000) (ψ := 1326617/1000000) 293 266
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t302 : ((100919675213/2000000000000 : ℚ) : ℝ) ≤ stT293 302 := by
  have hc : ((876899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).1
  have hw2 : ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((115087/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100919675213/2000000000000 : ℚ) : ℝ)
      = ((115087/2000000 : ℚ) : ℝ) * ((876899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c303 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((12601/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3674541/10000000) (δ := 14711/1000000000) (ψ := 1326617/1000000) 293 266
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t303 : ((3615945917/625000000000 : ℚ) : ℝ) ≤ stT293 303 := by
  have hc : ((25177/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).1
  have hw2 : ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143621/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3615945917/625000000000 : ℚ) : ℝ)
      = ((143621/2500000 : ℚ) : ℝ) * ((25177/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c304 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-760723/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1217611/2000000) (δ := 3673/250000000) (ψ := 1326617/1000000) 293 266
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t304 : ((-21818121171/500000000000 : ℚ) : ℝ) ≤ stT293 304 := by
  have hc : ((-760823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21818121171/500000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-760823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c305 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-967451/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3607189/5000000) (δ := 7359/500000000) (ψ := 1326617/1000000) 293 267
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t305 : ((-554018735049/10000000000000 : ℚ) : ℝ) ≤ stT293 305 := by
  have hc : ((-967551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).2
  have h0 : (0:ℝ) ≤ ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-554018735049/10000000000000 : ℚ) : ℝ)
      = ((572599/10000000 : ℚ) : ℝ) * ((-967551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c306 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-174193/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4816613/10000000) (δ := 2957/200000000) (ψ := 1326617/1000000) 293 267
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t306 : ((-49804050933/2500000000000 : ℚ) : ℝ) ≤ stT293 306 := by
  have hc : ((-174243/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).2
  have h0 : (0:ℝ) ≤ ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49804050933/2500000000000 : ℚ) : ℝ)
      = ((285831/5000000 : ℚ) : ℝ) * ((-174243/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c307 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((564719/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1213379/5000000) (δ := 7359/500000000) (ψ := 1326617/1000000) 293 267
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t307 : ((32224500187/1000000000000 : ℚ) : ℝ) ≤ stT293 307 := by
  have hc : ((564619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32224500187/1000000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((564619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c308 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((6249/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11167/2500000) (δ := 7359/500000000) (ψ := 1326617/1000000) 293 267
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t308 : ((14241346287/250000000000 : ℚ) : ℝ) ≤ stT293 308 := by
  have hc : ((49987/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14241346287/250000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((49987/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c309 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((149079/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2329731/10000000) (δ := 7409/500000000) (ψ := 1326617/1000000) 293 267
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t309 : ((529961497/15625000000 : ℚ) : ℝ) ≤ stT293 309 := by
  have hc : ((74527/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((529961497/15625000000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((74527/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c310 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-302943/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2348219/5000000) (δ := 2937/200000000) (ψ := 1326617/1000000) 293 267
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t310 : ((-86058454183/5000000000000 : ℚ) : ℝ) ≤ stT293 310 := by
  have hc : ((-303043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86058454183/5000000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-303043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c311 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-949439/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7055601/10000000) (δ := 7359/500000000) (ψ := 1326617/1000000) 293 267
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t311 : ((-67304273859/1250000000000 : ℚ) : ℝ) ≤ stT293 311 := by
  have hc : ((-949539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67304273859/1250000000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-949539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c312 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-20329/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6300891/10000000) (δ := 14677/1000000000) (ψ := 1326617/1000000) 293 268
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t312 : ((-23020910157/500000000000 : ℚ) : ℝ) ≤ stT293 312 := by
  have hc : ((-40663/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23020910157/500000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-40663/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c313 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-299/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3956891/10000000) (δ := 14677/1000000000) (ψ := 1326617/1000000) 293 268
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t313 : ((-170418051/250000000000 : ℚ) : ℝ) ≤ stT293 313 := by
  have hc : ((-603/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170418051/250000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-603/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c314 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((159441/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -810181/5000000) (δ := 7413/500000000) (ψ := 1326617/1000000) 293 268
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t314 : ((22491592943/500000000000 : ℚ) : ℝ) ≤ stT293 314 := by
  have hc : ((159421/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22491592943/500000000000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((159421/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c315 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((12001/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 22149/312500) (δ := 7363/500000000) (ψ := 1326617/1000000) 293 268
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t315 : ((6761091141/125000000000 : ℚ) : ℝ) ≤ stT293 315 := by
  have hc : ((47999/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6761091141/125000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((47999/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c316 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((4387/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6061/20000) (δ := 7363/500000000) (ψ := 1326617/1000000) 293 268
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t316 : ((9868691849/500000000000 : ℚ) : ℝ) ≤ stT293 316 := by
  have hc : ((17543/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9868691849/500000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((17543/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c317 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-26861/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2672417/5000000) (δ := 7413/500000000) (ψ := 1326617/1000000) 293 268
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t317 : ((-943090631/31250000000 : ℚ) : ℝ) ≤ stT293 317 := by
  have hc : ((-13433/25000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).2
  have h0 : (0:ℝ) ≤ ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-943090631/31250000000 : ℚ) : ℝ)
      = ((70207/1250000 : ℚ) : ℝ) * ((-13433/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c318 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-199347/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1912979/2500000) (δ := 7413/500000000) (ψ := 1326617/1000000) 293 268
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t318 : ((-111799630691/2000000000000 : ℚ) : ℝ) ≤ stT293 318 := by
  have hc : ((-199367/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111799630691/2000000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-199367/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c319 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-668107/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -359759/625000) (δ := 14733/1000000000) (ψ := 1326617/1000000) 293 269
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t319 : ((-374124421851/10000000000000 : ℚ) : ℝ) ≤ stT293 319 := by
  have hc : ((-668207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-374124421851/10000000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-668207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c320 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((18431/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1731783/5000000) (δ := 1477/100000000) (ψ := 1326617/1000000) 293 269
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t320 : ((1287204217/125000000000 : ℚ) : ℝ) ≤ stT293 320 := by
  have hc : ((18421/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).1
  have hw2 : ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69877/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1287204217/125000000000 : ℚ) : ℝ)
      = ((69877/1250000 : ℚ) : ℝ) * ((18421/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c321 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((891021/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1178019/10000000) (δ := 14733/1000000000) (ψ := 1326617/1000000) 293 269
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t321 : ((99452620309/2000000000000 : ℚ) : ℝ) ≤ stT293 321 := by
  have hc : ((890921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).1
  have hw2 : ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111629/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99452620309/2000000000000 : ℚ) : ℝ)
      = ((111629/2000000 : ℚ) : ℝ) * ((890921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c322 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((226173/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1100349/10000000) (δ := 14733/1000000000) (ψ := 1326617/1000000) 293 269
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t322 : ((15753413143/312500000000 : ℚ) : ℝ) ≤ stT293 322 := by
  have hc : ((56537/62500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15753413143/312500000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((56537/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c323 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((2203/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 674337/2000000) (δ := 14733/1000000000) (ψ := 1326617/1000000) 293 269
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t323 : ((306305907/25000000000 : ℚ) : ℝ) ≤ stT293 323 := by
  have hc : ((1101/5000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((306305907/25000000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((1101/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c324 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-157897/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5635989/10000000) (δ := 14733/1000000000) (ψ := 1326617/1000000) 293 269
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t324 : ((-10966814329/312500000000 : ℚ) : ℝ) ≤ stT293 324 := by
  have hc : ((-78961/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).2
  have h0 : (0:ℝ) ≤ ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10966814329/312500000000 : ℚ) : ℝ)
      = ((138889/2500000 : ℚ) : ℝ) * ((-78961/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c325 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-999877/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3907351/5000000) (δ := 371/25000000) (ψ := 1326617/1000000) 293 270
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t325 : ((-554688241877/10000000000000 : ℚ) : ℝ) ≤ stT293 325 := by
  have hc : ((-999977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).2
  have h0 : (0:ℝ) ≤ ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-554688241877/10000000000000 : ℚ) : ℝ)
      = ((554701/10000000 : ℚ) : ℝ) * ((-999977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c326 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-38069/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1391079/2500000) (δ := 14663/1000000000) (ψ := 1326617/1000000) 293 270
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t326 : ((-84351756549/2500000000000 : ℚ) : ℝ) ≤ stT293 326 := by
  have hc : ((-152301/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84351756549/2500000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-152301/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c327 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((240101/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -664163/2000000) (δ := 14663/1000000000) (ψ := 1326617/1000000) 293 270
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t327 : ((132720793001/10000000000000 : ℚ) : ℝ) ≤ stT293 327 := by
  have hc : ((240001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).1
  have hw2 : ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((553001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132720793001/10000000000000 : ℚ) : ℝ)
      = ((553001/10000000 : ℚ) : ℝ) * ((240001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c328 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((453719/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -542063/5000000) (δ := 737/50000000) (ψ := 1326617/1000000) 293 270
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t328 : ((250496514033/5000000000000 : ℚ) : ℝ) ≤ stT293 328 := by
  have hc : ((453669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).1
  have hw2 : ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((552157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250496514033/5000000000000 : ℚ) : ℝ)
      = ((552157/10000000 : ℚ) : ℝ) * ((453669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c329 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((896819/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1145677/10000000) (δ := 14663/1000000000) (ψ := 1326617/1000000) 293 270
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t329 : ((494376428923/10000000000000 : ℚ) : ℝ) ≤ stT293 329 := by
  have hc : ((896719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).1
  have hw2 : ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((551317/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((494376428923/10000000000000 : ℚ) : ℝ)
      = ((551317/10000000 : ℚ) : ℝ) * ((896719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c330 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((221449/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3368741/10000000) (δ := 14763/1000000000) (ψ := 1326617/1000000) 293 270
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t330 : ((121848418869/10000000000000 : ℚ) : ℝ) ≤ stT293 330 := by
  have hc : ((221349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121848418869/10000000000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((221349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c331 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-307833/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5585067/10000000) (δ := 371/25000000) (ψ := 1326617/1000000) 293 270
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t331 : ((-3384557819/100000000000 : ℚ) : ℝ) ≤ stT293 331 := by
  have hc : ((-307883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3384557819/100000000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-307883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c332 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-999719/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3897363/5000000) (δ := 14663/1000000000) (ψ := 1326617/1000000) 293 270
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t332 : ((-274361331609/5000000000000 : ℚ) : ℝ) ≤ stT293 332 := by
  have hc : ((-999819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274361331609/5000000000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-999819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c333 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-654333/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5710243/10000000) (δ := 14847/1000000000) (ψ := 1326617/1000000) 293 271
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t333 : ((-358627320701/10000000000000 : ℚ) : ℝ) ≤ stT293 333 := by
  have hc : ((-654433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).2
  have h0 : (0:ℝ) ≤ ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-358627320701/10000000000000 : ℚ) : ℝ)
      = ((547997/10000000 : ℚ) : ℝ) * ((-654433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c334 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((41127/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1756921/5000000) (δ := 14747/1000000000) (ψ := 1326617/1000000) 293 271
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t334 : ((449799737/50000000000 : ℚ) : ℝ) ≤ stT293 334 := by
  have hc : ((20551/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((449799737/50000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((20551/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c335 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((863017/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33099/250000) (δ := 14747/1000000000) (ψ := 1326617/1000000) 293 271
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t335 : ((235730803143/5000000000000 : ℚ) : ℝ) ≤ stT293 335 := by
  have hc : ((862917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235730803143/5000000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((862917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c336 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((14711/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 859329/10000000) (δ := 3689/250000000) (ψ := 1326617/1000000) 293 271
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t336 : ((16049290743/312500000000 : ℚ) : ℝ) ≤ stT293 336 := by
  have hc : ((235351/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16049290743/312500000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((235351/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c337 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((174417/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3036173/10000000) (δ := 14747/1000000000) (ψ := 1326617/1000000) 293 271
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t337 : ((47491816689/2500000000000 : ℚ) : ℝ) ≤ stT293 337 := by
  have hc : ((174367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).1
  have hw2 : ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((272367/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47491816689/2500000000000 : ℚ) : ℝ)
      = ((272367/5000000 : ℚ) : ℝ) * ((174367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c338 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-1959/4000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5206497/10000000) (δ := 229/15625000) (ψ := 1326617/1000000) 293 271
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t338 : ((-5328872413/200000000000 : ℚ) : ℝ) ≤ stT293 338 := by
  have hc : ((-9797/20000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).2
  have h0 : (0:ℝ) ≤ ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5328872413/200000000000 : ℚ) : ℝ)
      = ((543929/10000000 : ℚ) : ℝ) * ((-9797/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c339 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-12267/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3685261/5000000) (δ := 14747/1000000000) (ψ := 1326617/1000000) 293 271
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t339 : ((-13326411099/250000000000 : ℚ) : ℝ) ≤ stT293 339 := by
  have hc : ((-49073/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13326411099/250000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-49073/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c340 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-784041/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6179863/10000000) (δ := 14749/1000000000) (ψ := 1326617/1000000) 293 272
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t340 : ((-425260836107/10000000000000 : ℚ) : ℝ) ≤ stT293 340 := by
  have hc : ((-784141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-425260836107/10000000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-784141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c341 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-8131/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4028657/10000000) (δ := 14749/1000000000) (ψ := 1326617/1000000) 293 272
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t341 : ((-4414019181/2000000000000 : ℚ) : ℝ) ≤ stT293 341 := by
  have hc : ((-8151/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4414019181/2000000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-8151/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c342 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((729319/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1883677/10000000) (δ := 7327/500000000) (ψ := 1326617/1000000) 293 272
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t342 : ((197158211811/5000000000000 : ℚ) : ℝ) ≤ stT293 342 := by
  have hc : ((729219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).1
  have hw2 : ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((270369/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197158211811/5000000000000 : ℚ) : ℝ)
      = ((270369/5000000 : ℚ) : ℝ) * ((729219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c343 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((497401/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 255003/10000000) (δ := 14749/1000000000) (ψ := 1326617/1000000) 293 272
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t343 : ((268544175099/5000000000000 : ℚ) : ℝ) ≤ stT293 343 := by
  have hc : ((497351/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268544175099/5000000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((497351/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c344 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((577623/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2387457/10000000) (δ := 14749/1000000000) (ψ := 1326617/1000000) 293 272
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t344 : ((311379033249/10000000000000 : ℚ) : ℝ) ≤ stT293 344 := by
  have hc : ((577523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311379033249/10000000000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((577523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c345 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-116279/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2256879/5000000) (δ := 14749/1000000000) (ψ := 1326617/1000000) 293 272
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t345 : ((-31314719839/2500000000000 : ℚ) : ℝ) ≤ stT293 345 := by
  have hc : ((-116329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).2
  have h0 : (0:ℝ) ≤ ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31314719839/2500000000000 : ℚ) : ℝ)
      = ((269191/5000000 : ℚ) : ℝ) * ((-116329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c346 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-220811/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6633833/10000000) (δ := 7327/500000000) (ψ := 1326617/1000000) 293 272
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t346 : ((-7420144809/156250000000 : ℚ) : ℝ) ≤ stT293 346 := by
  have hc : ((-55209/62500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).2
  have h0 : (0:ℝ) ≤ ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7420144809/156250000000 : ℚ) : ℝ)
      = ((134401/2500000 : ℚ) : ℝ) * ((-55209/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c347 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-936761/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1392027/2000000) (δ := 7381/500000000) (ψ := 1326617/1000000) 293 273
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t347 : ((-502934153769/10000000000000 : ℚ) : ℝ) ≤ stT293 347 := by
  have hc : ((-936861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).2
  have h0 : (0:ℝ) ≤ ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-502934153769/10000000000000 : ℚ) : ℝ)
      = ((536829/10000000 : ℚ) : ℝ) * ((-936861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c348 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-361701/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -242611/500000) (δ := 7331/500000000) (ψ := 1326617/1000000) 293 273
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t348 : ((-193945958657/10000000000000 : ℚ) : ℝ) ≤ stT293 348 := by
  have hc : ((-361801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).2
  have h0 : (0:ℝ) ≤ ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193945958657/10000000000000 : ℚ) : ℝ)
      = ((536057/10000000 : ℚ) : ℝ) * ((-361801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c349 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((90697/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2750311/10000000) (δ := 7381/500000000) (ψ := 1326617/1000000) 293 273
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t349 : ((48538219299/2000000000000 : ℚ) : ℝ) ≤ stT293 349 := by
  have hc : ((90677/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48538219299/2000000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((90677/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c350 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((120741/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -327241/5000000) (δ := 7381/500000000) (ψ := 1326617/1000000) 293 273
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t350 : ((64532039277/1250000000000 : ℚ) : ℝ) ≤ stT293 350 := by
  have hc : ((241457/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).1
  have hw2 : ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((267261/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64532039277/1250000000000 : ℚ) : ℝ)
      = ((267261/5000000 : ℚ) : ℝ) * ((241457/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c351 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((419823/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1435413/10000000) (δ := 14841/1000000000) (ψ := 1326617/1000000) 293 273
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t351 : ((175045341/3906250000 : ℚ) : ℝ) ≤ stT293 351 := by
  have hc : ((419773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).1
  have hw2 : ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((834/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175045341/3906250000 : ℚ) : ℝ)
      = ((834/15625 : ℚ) : ℝ) * ((419773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c352 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((162353/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3519303/10000000) (δ := 7381/500000000) (ψ := 1326617/1000000) 293 273
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t352 : ((86481011253/10000000000000 : ℚ) : ℝ) ≤ stT293 352 := by
  have hc : ((162253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).1
  have hw2 : ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((533001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86481011253/10000000000000 : ℚ) : ℝ)
      = ((533001/10000000 : ℚ) : ℝ) * ((162253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c353 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-154881/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1399333/2500000) (δ := 7331/500000000) (ψ := 1326617/1000000) 293 273
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t353 : ((-41224126891/1250000000000 : ℚ) : ℝ) ≤ stT293 353 := by
  have hc : ((-77453/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41224126891/1250000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-77453/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c354 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-997279/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7669501/10000000) (δ := 14741/1000000000) (ψ := 1326617/1000000) 293 273
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t354 : ((-106020390321/2000000000000 : ℚ) : ℝ) ≤ stT293 354 := by
  have hc : ((-997379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).2
  have h0 : (0:ℝ) ≤ ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106020390321/2000000000000 : ℚ) : ℝ)
      = ((106299/2000000 : ℚ) : ℝ) * ((-997379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c355 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-182461/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2986113/5000000) (δ := 14669/1000000000) (ψ := 1326617/1000000) 293 274
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t355 : ((-9685353207/250000000000 : ℚ) : ℝ) ≤ stT293 355 := by
  have hc : ((-91243/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9685353207/250000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-91243/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c356 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((1223/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -488963/1250000) (δ := 7417/500000000) (ψ := 1326617/1000000) 293 274
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t356 : ((318793797/1000000000000 : ℚ) : ℝ) ≤ stT293 356 := by
  have hc : ((1203/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).1
  have hw2 : ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((264999/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((318793797/1000000000000 : ℚ) : ℝ)
      = ((264999/5000000 : ℚ) : ℝ) * ((1203/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c357 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((736567/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1857041/10000000) (δ := 14669/1000000000) (ψ := 1326617/1000000) 293 274
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t357 : ((48722447319/1250000000000 : ℚ) : ℝ) ≤ stT293 357 := by
  have hc : ((736467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48722447319/1250000000000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((736467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c358 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((199411/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47977/2500000) (δ := 14669/1000000000) (ψ := 1326617/1000000) 293 274
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t358 : ((26345333439/500000000000 : ℚ) : ℝ) ≤ stT293 358 := by
  have hc : ((199391/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).1
  have hw2 : ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((132129/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26345333439/500000000000 : ℚ) : ℝ)
      = ((132129/2500000 : ℚ) : ℝ) * ((199391/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c359 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((313127/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2235143/10000000) (δ := 7417/500000000) (ψ := 1326617/1000000) 293 274
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t359 : ((165235465983/5000000000000 : ℚ) : ℝ) ≤ stT293 359 := by
  have hc : ((313077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165235465983/5000000000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((313077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c360 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-137859/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4272739/10000000) (δ := 14769/1000000000) (ψ := 1326617/1000000) 293 274
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t360 : ((-72710877073/10000000000000 : ℚ) : ℝ) ≤ stT293 360 := by
  have hc : ((-137959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).2
  have h0 : (0:ℝ) ≤ ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72710877073/10000000000000 : ℚ) : ℝ)
      = ((527047/10000000 : ℚ) : ℝ) * ((-137959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c361 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-814027/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 315231/500000) (δ := 7417/500000000) (ψ := 1326617/1000000) 293 274
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t361 : ((-107122016533/2500000000000 : ℚ) : ℝ) ≤ stT293 361 := by
  have hc : ((-814127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).2
  have h0 : (0:ℝ) ≤ ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107122016533/2500000000000 : ℚ) : ℝ)
      = ((131579/2500000 : ℚ) : ℝ) * ((-814127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c362 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-30683/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1844257/2500000) (δ := 3669/250000000) (ψ := 1326617/1000000) 293 275
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t362 : ((-129026318021/2500000000000 : ℚ) : ℝ) ≤ stT293 362 := by
  have hc : ((-245489/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).2
  have h0 : (0:ℝ) ≤ ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129026318021/2500000000000 : ℚ) : ℝ)
      = ((525589/10000000 : ℚ) : ℝ) * ((-245489/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c363 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-541101/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2678177/5000000) (δ := 14827/1000000000) (ψ := 1326617/1000000) 293 275
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t363 : ((-4438389401/156250000000 : ℚ) : ℝ) ≤ stT293 363 := by
  have hc : ((-541201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4438389401/156250000000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-541201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c364 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((1451/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1670623/5000000) (δ := 3669/250000000) (ψ := 1326617/1000000) 293 275
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t364 : ((3040809813/250000000000 : ℚ) : ℝ) ≤ stT293 364 := by
  have hc : ((11603/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).1
  have hw2 : ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3040809813/250000000000 : ℚ) : ℝ)
      = ((262071/5000000 : ℚ) : ℝ) * ((11603/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c365 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((861463/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83227/625000) (δ := 1847/125000000) (ψ := 1326617/1000000) 293 275
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t365 : ((450857205549/10000000000000 : ℚ) : ℝ) ≤ stT293 365 := by
  have hc : ((861363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).1
  have hw2 : ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((523423/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((450857205549/10000000000000 : ℚ) : ℝ)
      = ((523423/10000000 : ℚ) : ℝ) * ((861363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c366 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((482019/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 84061/1250000) (δ := 1847/125000000) (ψ := 1326617/1000000) 293 275
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t366 : ((62982263013/1250000000000 : ℚ) : ℝ) ≤ stT293 366 := by
  have hc : ((481969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).1
  have hw2 : ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((130677/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62982263013/1250000000000 : ℚ) : ℝ)
      = ((130677/2500000 : ℚ) : ℝ) * ((481969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c367 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((481487/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1335557/5000000) (δ := 3669/250000000) (ψ := 1326617/1000000) 293 275
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t367 : ((50256321413/2000000000000 : ℚ) : ℝ) ≤ stT293 367 := by
  have hc : ((481387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).1
  have hw2 : ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((104399/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50256321413/2000000000000 : ℚ) : ℝ)
      = ((104399/2000000 : ℚ) : ℝ) * ((481387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c368 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-145337/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7288/15625) (δ := 1847/125000000) (ψ := 1326617/1000000) 293 275
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t368 : ((-75788353069/5000000000000 : ℚ) : ℝ) ≤ stT293 368 := by
  have hc : ((-145387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).2
  have h0 : (0:ℝ) ≤ ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75788353069/5000000000000 : ℚ) : ℝ)
      = ((521287/10000000 : ℚ) : ℝ) * ((-145387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c369 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-110831/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1330421/2000000) (δ := 3669/250000000) (ψ := 1326617/1000000) 293 275
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t369 : ((-5770290923/125000000000 : ℚ) : ℝ) ≤ stT293 369 := by
  have hc : ((-221687/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).2
  have h0 : (0:ℝ) ≤ ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5770290923/125000000000 : ℚ) : ℝ)
      = ((26029/500000 : ℚ) : ℝ) * ((-221687/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c370 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-951653/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -353671/500000) (δ := 14783/1000000000) (ψ := 1326617/1000000) 293 276
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t370 : ((-123698385657/2500000000000 : ℚ) : ℝ) ≤ stT293 370 := by
  have hc : ((-951753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123698385657/2500000000000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-951753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c371 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-112723/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5096403/10000000) (δ := 23/1562500) (ψ := 1326617/1000000) 293 276
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t371 : ((-585359429/25000000000 : ℚ) : ℝ) ≤ stT293 371 := by
  have hc : ((-28187/62500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-585359429/25000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-28187/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c372 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((78863/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3124659/10000000) (δ := 14783/1000000000) (ψ := 1326617/1000000) 293 276
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t372 : ((817510641/50000000000 : ℚ) : ℝ) ≤ stT293 372 := by
  have hc : ((39419/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).1
  have hw2 : ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((20739/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((817510641/50000000000 : ℚ) : ℝ)
      = ((20739/400000 : ℚ) : ℝ) * ((39419/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c373 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((894593/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115819/1000000) (δ := 23/1562500) (ψ := 1326617/1000000) 293 276
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t373 : ((23157529277/500000000000 : ℚ) : ℝ) ≤ stT293 373 := by
  have hc : ((894493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).1
  have hw2 : ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25889/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23157529277/500000000000 : ℚ) : ℝ)
      = ((25889/500000 : ℚ) : ℝ) * ((894493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c374 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((474433/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 200733/2500000) (δ := 741/50000000) (ψ := 1326617/1000000) 293 276
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t374 : ((245297282321/5000000000000 : ℚ) : ℝ) ≤ stT293 374 := by
  have hc : ((474383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).1
  have hw2 : ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((517087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245297282321/5000000000000 : ℚ) : ℝ)
      = ((517087/10000000 : ℚ) : ℝ) * ((474383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c375 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((450411/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2758927/10000000) (δ := 23/1562500) (ψ := 1326617/1000000) 293 276
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t375 : ((232539249467/10000000000000 : ℚ) : ℝ) ≤ stT293 375 := by
  have hc : ((450311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232539249467/10000000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((450311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c376 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-153987/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 294353/625000) (δ := 14683/1000000000) (ψ := 1326617/1000000) 293 276
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t376 : ((-79438575307/5000000000000 : ℚ) : ℝ) ≤ stT293 376 := by
  have hc : ((-154037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).2
  have h0 : (0:ℝ) ≤ ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79438575307/5000000000000 : ℚ) : ℝ)
      = ((515711/10000000 : ℚ) : ℝ) * ((-154037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c377 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-443607/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 103987/156250) (δ := 14683/1000000000) (ψ := 1326617/1000000) 293 276
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t377 : ((-228495333739/5000000000000 : ℚ) : ℝ) ≤ stT293 377 := by
  have hc : ((-443657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).2
  have h0 : (0:ℝ) ≤ ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228495333739/5000000000000 : ℚ) : ℝ)
      = ((515027/10000000 : ℚ) : ℝ) * ((-443657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c378 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-956327/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7112403/10000000) (δ := 14713/1000000000) (ψ := 1326617/1000000) 293 277
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t378 : ((-98386689063/2000000000000 : ℚ) : ℝ) ≤ stT293 378 := by
  have hc : ((-956427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).2
  have h0 : (0:ℝ) ≤ ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98386689063/2000000000000 : ℚ) : ℝ)
      = ((102869/2000000 : ℚ) : ℝ) * ((-956427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c379 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-119863/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1035413/2000000) (δ := 14813/1000000000) (ψ := 1326617/1000000) 293 277
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t379 : ((-1924449669/78125000000 : ℚ) : ℝ) ≤ stT293 379 := by
  have hc : ((-7493/15625 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1924449669/78125000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-7493/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c380 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((268683/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3246927/10000000) (δ := 1469/100000000) (ψ := 1326617/1000000) 293 277
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t380 : ((137780124587/10000000000000 : ℚ) : ℝ) ≤ stT293 380 := by
  have hc : ((268583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).1
  have hw2 : ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137780124587/10000000000000 : ℚ) : ℝ)
      = ((512989/10000000 : ℚ) : ℝ) * ((268583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c381 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((172689/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -330461/2500000) (δ := 14713/1000000000) (ψ := 1326617/1000000) 293 277
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t381 : ((17692183747/400000000000 : ℚ) : ℝ) ≤ stT293 381 := by
  have hc : ((172669/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).1
  have hw2 : ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102463/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17692183747/400000000000 : ℚ) : ℝ)
      = ((102463/2000000 : ℚ) : ℝ) * ((172669/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c382 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((971503/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 299129/5000000) (δ := 14813/1000000000) (ψ := 1326617/1000000) 293 277
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t382 : ((124253129133/2500000000000 : ℚ) : ℝ) ≤ stT293 382 := by
  have hc : ((971403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124253129133/2500000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((971403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c383 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((535841/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2513233/10000000) (δ := 14713/1000000000) (ψ := 1326617/1000000) 293 277
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t383 : ((267334759/9765625000 : ℚ) : ℝ) ≤ stT293 383 := by
  have hc : ((535741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267334759/9765625000 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((535741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c384 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-98611/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44233/100000) (δ := 14713/1000000000) (ψ := 1326617/1000000) 293 277
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t384 : ((-50347793571/5000000000000 : ℚ) : ℝ) ≤ stT293 384 := by
  have hc : ((-98661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).2
  have h0 : (0:ℝ) ≤ ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50347793571/5000000000000 : ℚ) : ℝ)
      = ((510311/10000000 : ℚ) : ℝ) * ((-98661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c385 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-102439/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3164193/5000000) (δ := 14713/1000000000) (ψ := 1326617/1000000) 293 277
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t385 : ((-6526775259/156250000000 : ℚ) : ℝ) ≤ stT293 385 := by
  have hc : ((-204903/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).2
  have h0 : (0:ℝ) ≤ ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6526775259/156250000000 : ℚ) : ℝ)
      = ((31853/625000 : ℚ) : ℝ) * ((-204903/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c386 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-618/625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -467467/625000) (δ := 14697/1000000000) (ψ := 1326617/1000000) 293 278
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t386 : ((-5033372443/100000000000 : ℚ) : ℝ) ≤ stT293 386 := by
  have hc : ((-9889/10000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5033372443/100000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-9889/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c387 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-76927/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -223371/400000) (δ := 7353/500000000) (ψ := 1326617/1000000) 293 278
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t387 : ((-78221158191/2500000000000 : ℚ) : ℝ) ≤ stT293 387 := by
  have hc : ((-153879/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78221158191/2500000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-153879/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c388 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((93097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -461739/1250000) (δ := 14697/1000000000) (ψ := 1326617/1000000) 293 278
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t388 : ((47212065981/10000000000000 : ℚ) : ℝ) ≤ stT293 388 := by
  have hc : ((92997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).1
  have hw2 : ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47212065981/10000000000000 : ℚ) : ℝ)
      = ((507673/10000000 : ℚ) : ℝ) * ((92997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c389 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((749571/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1808457/10000000) (δ := 14697/1000000000) (ψ := 1326617/1000000) 293 278
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t389 : ((18999839321/500000000000 : ℚ) : ℝ) ≤ stT293 389 := by
  have hc : ((749471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).1
  have hw2 : ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25351/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18999839321/500000000000 : ℚ) : ℝ)
      = ((25351/500000 : ℚ) : ℝ) * ((749471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c390 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((999583/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72163/10000000) (δ := 7403/500000000) (ψ := 1326617/1000000) 293 278
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t390 : ((506107207227/10000000000000 : ℚ) : ℝ) ≤ stT293 390 := by
  have hc : ((999483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((506107207227/10000000000000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((999483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c391 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((71149/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1947949/10000000) (δ := 7403/500000000) (ψ := 1326617/1000000) 293 278
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t391 : ((35976486219/1000000000000 : ℚ) : ℝ) ≤ stT293 391 := by
  have hc : ((71139/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35976486219/1000000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((71139/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c392 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((43193/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1909487/5000000) (δ := 7353/500000000) (ψ := 1326617/1000000) 293 278
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t392 : ((5441310017/2500000000000 : ℚ) : ℝ) ≤ stT293 392 := by
  have hc : ((43093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5441310017/2500000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((43093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c393 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-646737/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2842619/5000000) (δ := 14797/1000000000) (ψ := 1326617/1000000) 293 278
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t393 : ((-163143287629/5000000000000 : ℚ) : ℝ) ≤ stT293 393 := by
  have hc : ((-646837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).2
  have h0 : (0:ℝ) ≤ ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163143287629/5000000000000 : ℚ) : ℝ)
      = ((252217/5000000 : ℚ) : ℝ) * ((-646837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c394 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-496229/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 377337/500000) (δ := 14697/1000000000) (ψ := 1326617/1000000) 293 278
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t394 : ((-250021886247/5000000000000 : ℚ) : ℝ) ≤ stT293 394 := by
  have hc : ((-496279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).2
  have h0 : (0:ℝ) ≤ ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250021886247/5000000000000 : ℚ) : ℝ)
      = ((503793/10000000 : ℚ) : ℝ) * ((-496279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c395 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-162799/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3152241/5000000) (δ := 2961/200000000) (ψ := 1326617/1000000) 293 279
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t395 : ((-16384638789/400000000000 : ℚ) : ℝ) ≤ stT293 395 := by
  have hc : ((-162819/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16384638789/400000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-162819/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c396 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-208603/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1113089/2500000) (δ := 2941/200000000) (ψ := 1326617/1000000) 293 279
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t396 : ((-104877222857/10000000000000 : ℚ) : ℝ) ≤ stT293 396 := by
  have hc : ((-208703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104877222857/10000000000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-208703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c397 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((252249/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2604991/10000000) (δ := 2941/200000000) (ψ := 1326617/1000000) 293 279
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t397 : ((25314979023/1000000000000 : ℚ) : ℝ) ≤ stT293 397 := by
  have hc : ((252199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).1
  have hw2 : ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((100377/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25314979023/1000000000000 : ℚ) : ℝ)
      = ((100377/2000000 : ℚ) : ℝ) * ((252199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c398 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((953887/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -95271/1250000) (δ := 7399/500000000) (ψ := 1326617/1000000) 293 279
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t398 : ((239044774449/5000000000000 : ℚ) : ℝ) ≤ stT293 398 := by
  have hc : ((953787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).1
  have hw2 : ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250627/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239044774449/5000000000000 : ℚ) : ℝ)
      = ((250627/5000000 : ℚ) : ℝ) * ((953787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c399 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((227201/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8406/78125) (δ := 2941/200000000) (ψ := 1326617/1000000) 293 279
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t399 : ((7108138261/156250000000 : ℚ) : ℝ) ≤ stT293 399 := by
  have hc : ((28397/31250 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).1
  have hw2 : ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7108138261/156250000000 : ℚ) : ℝ)
      = ((250313/5000000 : ℚ) : ℝ) * ((28397/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c400 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((395857/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2909489/10000000) (δ := 2961/200000000) (ψ := 1326617/1000000) 293 279
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t400 : ((395757/20000000 : ℚ) : ℝ) ≤ stT293 400 := by
  have hc : ((395757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).1
  have hw2 : ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/20 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((395757/20000000 : ℚ) : ℝ)
      = ((1/20 : ℚ) : ℝ) * ((395757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c401 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-318921/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1184617/2500000) (δ := 2941/200000000) (ψ := 1326617/1000000) 293 279
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t401 : ((-159311749917/10000000000000 : ℚ) : ℝ) ≤ stT293 401 := by
  have hc : ((-319021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159311749917/10000000000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-319021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c402 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-869573/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 410177/625000) (δ := 7399/500000000) (ψ := 1326617/1000000) 293 279
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t402 : ((-86750751423/2000000000000 : ℚ) : ℝ) ≤ stT293 402 := by
  have hc : ((-869673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86750751423/2000000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-869673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c403 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-977717/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1465047/2000000) (δ := 14791/1000000000) (ψ := 1326617/1000000) 293 280
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t403 : ((-60885731139/1250000000000 : ℚ) : ℝ) ≤ stT293 403 := by
  have hc : ((-977817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60885731139/1250000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-977817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c404 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-147923/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137747/250000) (δ := 14691/1000000000) (ψ := 1326617/1000000) 293 280
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t404 : ((-18401735253/625000000000 : ℚ) : ℝ) ≤ stT293 404 := by
  have hc : ((-36987/62500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18401735253/625000000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-36987/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c405 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((91073/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3698993/10000000) (δ := 3703/250000000) (ψ := 1326617/1000000) 293 280
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t405 : ((45204756619/10000000000000 : ℚ) : ℝ) ≤ stT293 405 := by
  have hc : ((90973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45204756619/10000000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((90973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c406 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((726879/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -75703/400000) (δ := 1839/125000000) (ψ := 1326617/1000000) 293 280
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t406 : ((360693876689/10000000000000 : ℚ) : ℝ) ≤ stT293 406 := by
  have hc : ((726779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((360693876689/10000000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((726779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c407 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((999343/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29/3200) (δ := 1839/125000000) (ψ := 1326617/1000000) 293 280
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t407 : ((495305769483/10000000000000 : ℚ) : ℝ) ≤ stT293 407 := by
  have hc : ((999243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((495305769483/10000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((999243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c408 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((775827/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 170693/1000000) (δ := 1839/125000000) (ψ := 1326617/1000000) 293 280
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t408 : ((384041493071/10000000000000 : ℚ) : ℝ) ≤ stT293 408 := by
  have hc : ((775727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((384041493071/10000000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((775727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c409 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((42483/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 350009/1000000) (δ := 1839/125000000) (ψ := 1326617/1000000) 293 280
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t409 : ((2624265293/312500000000 : ℚ) : ℝ) ≤ stT293 409 := by
  have hc : ((21229/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2624265293/312500000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((21229/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c410 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-518201/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1057771/2000000) (δ := 1839/125000000) (ψ := 1326617/1000000) 293 280
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t410 : ((-51194144673/2000000000000 : ℚ) : ℝ) ≤ stT293 410 := by
  have hc : ((-518301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).2
  have h0 : (0:ℝ) ≤ ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51194144673/2000000000000 : ℚ) : ℝ)
      = ((98773/2000000 : ℚ) : ℝ) * ((-518301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c411 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-475819/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3536649/5000000) (δ := 14691/1000000000) (ψ := 1326617/1000000) 293 280
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t411 : ((-14670565401/312500000000 : ℚ) : ℝ) ≤ stT293 411 := by
  have hc : ((-475869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14670565401/312500000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-475869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c412 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-23029/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6854617/10000000) (δ := 3671/250000000) (ψ := 1326617/1000000) 293 281
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t412 : ((-4538725579/100000000000 : ℚ) : ℝ) ≤ stT293 412 := by
  have hc : ((-46063/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).2
  have h0 : (0:ℝ) ≤ ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4538725579/100000000000 : ℚ) : ℝ)
      = ((98533/2000000 : ℚ) : ℝ) * ((-46063/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c413 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-444629/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -507889/1000000) (δ := 14819/1000000000) (ψ := 1326617/1000000) 293 281
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t413 : ((-54709227393/2500000000000 : ℚ) : ℝ) ≤ stT293 413 := by
  have hc : ((-444729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54709227393/2500000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-444729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c414 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((122651/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -826853/2500000) (δ := 14819/1000000000) (ψ := 1326617/1000000) 293 281
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t414 : ((60255081273/5000000000000 : ℚ) : ℝ) ≤ stT293 414 := by
  have hc : ((122601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).1
  have hw2 : ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((491473/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60255081273/5000000000000 : ℚ) : ℝ)
      = ((491473/10000000 : ℚ) : ℝ) * ((122601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c415 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((408077/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1540183/10000000) (δ := 3671/250000000) (ψ := 1326617/1000000) 293 281
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t415 : ((312956709/7812500000 : ℚ) : ℝ) ≤ stT293 415 := by
  have hc : ((408027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).1
  have hw2 : ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((767/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((312956709/7812500000 : ℚ) : ℝ)
      = ((767/15625 : ℚ) : ℝ) * ((408027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c416 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((498017/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8909/400000) (δ := 14719/1000000000) (ψ := 1326617/1000000) 293 281
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t416 : ((24414824043/500000000000 : ℚ) : ℝ) ≤ stT293 416 := by
  have hc : ((497967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).1
  have hw2 : ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24414824043/500000000000 : ℚ) : ℝ)
      = ((49029/1000000 : ℚ) : ℝ) * ((497967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c417 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((87751/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1981457/10000000) (δ := 231/15625000) (ψ := 1326617/1000000) 293 281
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t417 : ((42965718927/1250000000000 : ℚ) : ℝ) ≤ stT293 417 := by
  have hc : ((175477/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).1
  have hw2 : ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((244851/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42965718927/1250000000000 : ℚ) : ℝ)
      = ((244851/5000000 : ℚ) : ℝ) * ((175477/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c418 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((38173/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3735941/10000000) (δ := 231/15625000) (ψ := 1326617/1000000) 293 281
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t418 : ((3729306229/1000000000000 : ℚ) : ℝ) ≤ stT293 418 := by
  have hc : ((38123/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3729306229/1000000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((38123/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c419 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-292023/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4389/8000) (δ := 3671/250000000) (ψ := 1326617/1000000) 293 281
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t419 : ((-35671751709/1250000000000 : ℚ) : ℝ) ≤ stT293 419 := by
  have hc : ((-292073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).2
  have h0 : (0:ℝ) ≤ ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35671751709/1250000000000 : ℚ) : ℝ)
      = ((122133/2500000 : ℚ) : ℝ) * ((-292073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c420 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-30289/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56503/78125) (δ := 14819/1000000000) (ψ := 1326617/1000000) 293 281
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t420 : ((-118248581487/2500000000000 : ℚ) : ℝ) ≤ stT293 420 := by
  have hc : ((-242337/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).2
  have h0 : (0:ℝ) ≤ ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118248581487/2500000000000 : ℚ) : ℝ)
      = ((487951/10000000 : ℚ) : ℝ) * ((-242337/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c421 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-901253/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6733621/10000000) (δ := 7413/500000000) (ψ := 1326617/1000000) 293 282
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t421 : ((-439293312963/10000000000000 : ℚ) : ℝ) ≤ stT293 421 := by
  have hc : ((-901353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).2
  have h0 : (0:ℝ) ≤ ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-439293312963/10000000000000 : ℚ) : ℝ)
      = ((487371/10000000 : ℚ) : ℝ) * ((-901353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c422 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-207303/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -999153/2000000) (δ := 7363/500000000) (ψ := 1326617/1000000) 293 282
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t422 : ((-100937988929/5000000000000 : ℚ) : ℝ) ≤ stT293 422 := by
  have hc : ((-207353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).2
  have h0 : (0:ℝ) ≤ ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100937988929/5000000000000 : ℚ) : ℝ)
      = ((486793/10000000 : ℚ) : ℝ) * ((-207353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c423 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((131419/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -815521/2500000) (δ := 7363/500000000) (ψ := 1326617/1000000) 293 282
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t423 : ((7984213713/625000000000 : ℚ) : ℝ) ≤ stT293 423 := by
  have hc : ((131369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7984213713/625000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((131369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c424 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((817941/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -95777/625000) (δ := 14677/1000000000) (ψ := 1326617/1000000) 293 282
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t424 : ((198588969461/5000000000000 : ℚ) : ℝ) ≤ stT293 424 := by
  have hc : ((817841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198588969461/5000000000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((817841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c425 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((498509/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96559/5000000) (δ := 14777/1000000000) (ψ := 1326617/1000000) 293 282
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t425 : ((241788005589/5000000000000 : ℚ) : ℝ) ≤ stT293 425 := by
  have hc : ((498459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).1
  have hw2 : ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((485071/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((241788005589/5000000000000 : ℚ) : ℝ)
      = ((485071/10000000 : ℚ) : ℝ) * ((498459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c426 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((720789/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23933/125000) (δ := 7363/500000000) (ψ := 1326617/1000000) 293 282
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t426 : ((349174541189/10000000000000 : ℚ) : ℝ) ≤ stT293 426 := by
  have hc : ((720689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).1
  have hw2 : ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((484501/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((349174541189/10000000000000 : ℚ) : ℝ)
      = ((484501/10000000 : ℚ) : ℝ) * ((720689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c427 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((11767/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3632133/10000000) (δ := 7413/500000000) (ψ := 1326617/1000000) 293 282
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t427 : ((5689600281/1000000000000 : ℚ) : ℝ) ≤ stT293 427 := by
  have hc : ((11757/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).1
  have hw2 : ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((483933/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5689600281/1000000000000 : ℚ) : ℝ)
      = ((483933/10000000 : ℚ) : ℝ) * ((11757/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c428 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-134363/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5345523/10000000) (δ := 14777/1000000000) (ψ := 1326617/1000000) 293 282
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t428 : ((-16239748293/625000000000 : ℚ) : ℝ) ≤ stT293 428 := by
  have hc : ((-33597/62500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16239748293/625000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-33597/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c429 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-949367/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 881879/1250000) (δ := 7363/500000000) (ψ := 1326617/1000000) 293 282
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t429 : ((-91681482987/2000000000000 : ℚ) : ℝ) ≤ stT293 429 := by
  have hc : ((-949467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91681482987/2000000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-949467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c430 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-467487/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1736863/2500000) (δ := 1477/100000000) (ψ := 1326617/1000000) 293 283
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t430 : ((-225466445491/5000000000000 : ℚ) : ℝ) ≤ stT293 430 := by
  have hc : ((-467537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225466445491/5000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-467537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c431 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-100693/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5246001/10000000) (δ := 1477/100000000) (ψ := 1326617/1000000) 293 283
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t431 : ((-12127960173/500000000000 : ℚ) : ℝ) ≤ stT293 431 := by
  have hc : ((-100713/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).2
  have h0 : (0:ℝ) ≤ ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12127960173/500000000000 : ℚ) : ℝ)
      = ((120421/2500000 : ℚ) : ℝ) * ((-100713/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c432 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((75423/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -221777/625000) (δ := 1467/100000000) (ψ := 1326617/1000000) 293 283
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t432 : ((290110677/40000000000 : ℚ) : ℝ) ≤ stT293 432 := by
  have hc : ((75373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((290110677/40000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((75373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c433 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((737187/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -370949/2000000) (δ := 14833/1000000000) (ψ := 1326617/1000000) 293 283
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t433 : ((354221162503/10000000000000 : ℚ) : ℝ) ≤ stT293 433 := by
  have hc : ((737087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((354221162503/10000000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((737087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c434 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((498911/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -82507/5000000) (δ := 14833/1000000000) (ψ := 1326617/1000000) 293 283
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t434 : ((47892152583/1000000000000 : ℚ) : ℝ) ≤ stT293 434 := by
  have hc : ((498861/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47892152583/1000000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((498861/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c435 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((410301/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 760417/5000000) (δ := 1477/100000000) (ψ := 1326617/1000000) 293 283
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t435 : ((196700175213/5000000000000 : ℚ) : ℝ) ≤ stT293 435 := by
  have hc : ((410251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196700175213/5000000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((410251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c436 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((142821/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3202801/10000000) (δ := 14733/1000000000) (ψ := 1326617/1000000) 293 283
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t436 : ((68374887923/5000000000000 : ℚ) : ℝ) ≤ stT293 436 := by
  have hc : ((142771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68374887923/5000000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((142771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c437 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-372367/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 976177/2000000) (δ := 1467/100000000) (ψ := 1326617/1000000) 293 283
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t437 : ((-35635035291/2000000000000 : ℚ) : ℝ) ≤ stT293 437 := by
  have hc : ((-372467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35635035291/2000000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-372467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c438 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-217017/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3277617/5000000) (δ := 14833/1000000000) (ψ := 1326617/1000000) 293 283
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t438 : ((-51853395699/1250000000000 : ℚ) : ℝ) ≤ stT293 438 := by
  have hc : ((-108521/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51853395699/1250000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-108521/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c439 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-494483/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7482263/10000000) (δ := 14841/1000000000) (ψ := 1326617/1000000) 293 284
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t439 : ((-118013871521/2500000000000 : ℚ) : ℝ) ≤ stT293 439 := by
  have hc : ((-494533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118013871521/2500000000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-494533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c440 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-685613/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2907803/5000000) (δ := 14741/1000000000) (ψ := 1326617/1000000) 293 284
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t440 : ((-81725332479/2500000000000 : ℚ) : ℝ) ≤ stT293 440 := by
  have hc : ((-685713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81725332479/2500000000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-685713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c441 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-11273/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2076379/5000000) (δ := 7331/500000000) (ψ := 1326617/1000000) 293 284
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t441 : ((-10748107061/2500000000000 : ℚ) : ℝ) ≤ stT293 441 := by
  have hc : ((-22571/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10748107061/2500000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-22571/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c442 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((13561/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -498729/2000000) (δ := 14841/1000000000) (ψ := 1326617/1000000) 293 284
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t442 : ((12898228167/500000000000 : ℚ) : ℝ) ≤ stT293 442 := by
  have hc : ((27117/50000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).1
  have hw2 : ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((475651/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12898228167/500000000000 : ℚ) : ℝ)
      = ((475651/10000000 : ℚ) : ℝ) * ((27117/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c443 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((944309/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -838269/10000000) (δ := 7381/500000000) (ψ := 1326617/1000000) 293 284
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t443 : ((224303457413/5000000000000 : ℚ) : ℝ) ≤ stT293 443 := by
  have hc : ((944209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).1
  have hw2 : ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237557/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224303457413/5000000000000 : ℚ) : ℝ)
      = ((237557/5000000 : ℚ) : ℝ) * ((944209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c444 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((947539/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 203343/2500000) (δ := 7381/500000000) (ψ := 1326617/1000000) 293 284
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t444 : ((224816852871/5000000000000 : ℚ) : ℝ) ≤ stT293 444 := by
  have hc : ((947439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).1
  have hw2 : ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237289/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224816852871/5000000000000 : ℚ) : ℝ)
      = ((237289/5000000 : ℚ) : ℝ) * ((947439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c445 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((55327/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1230639/5000000) (δ := 14841/1000000000) (ψ := 1326617/1000000) 293 284
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t445 : ((5244549453/200000000000 : ℚ) : ℝ) ≤ stT293 445 := by
  have hc : ((55317/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5244549453/200000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((55317/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c446 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-71351/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51319/125000) (δ := 7381/500000000) (ψ := 1326617/1000000) 293 284
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t446 : ((-16916524407/5000000000000 : ℚ) : ℝ) ≤ stT293 446 := by
  have hc : ((-71451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).2
  have h0 : (0:ℝ) ≤ ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16916524407/5000000000000 : ℚ) : ℝ)
      = ((236757/5000000 : ℚ) : ℝ) * ((-71451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c447 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-66509/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5746027/10000000) (δ := 7381/500000000) (ψ := 1326617/1000000) 293 284
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t447 : ((-3932802837/125000000000 : ℚ) : ℝ) ≤ stT293 447 := by
  have hc : ((-66519/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).2
  have h0 : (0:ℝ) ≤ ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3932802837/125000000000 : ℚ) : ℝ)
      = ((59123/1250000 : ℚ) : ℝ) * ((-66519/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c448 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-491151/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1476589/2000000) (δ := 7331/500000000) (ψ := 1326617/1000000) 293 284
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t448 : ((-29008857457/625000000000 : ℚ) : ℝ) ≤ stT293 448 := by
  have hc : ((-491201/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).2
  have h0 : (0:ℝ) ≤ ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29008857457/625000000000 : ℚ) : ℝ)
      = ((59057/1250000 : ℚ) : ℝ) * ((-491201/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c449 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-178777/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1672959/2500000) (δ := 3687/250000000) (ψ := 1326617/1000000) 293 285
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t449 : ((-8437966821/200000000000 : ℚ) : ℝ) ≤ stT293 449 := by
  have hc : ((-178797/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).2
  have h0 : (0:ℝ) ≤ ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8437966821/200000000000 : ℚ) : ℝ)
      = ((47193/1000000 : ℚ) : ℝ) * ((-178797/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c450 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-219327/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5062243/10000000) (δ := 29/1953125) (ψ := 1326617/1000000) 293 285
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t450 : ((-20683082937/1000000000000 : ℚ) : ℝ) ≤ stT293 450 := by
  have hc : ((-219377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).2
  have h0 : (0:ℝ) ≤ ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20683082937/1000000000000 : ℚ) : ℝ)
      = ((94281/2000000 : ℚ) : ℝ) * ((-219377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c451 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((97521/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42953/125000) (δ := 2931/200000000) (ψ := 1326617/1000000) 293 285
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t451 : ((45897241951/5000000000000 : ℚ) : ℝ) ≤ stT293 451 := by
  have hc : ((97471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).1
  have hw2 : ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((470881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45897241951/5000000000000 : ℚ) : ℝ)
      = ((470881/10000000 : ℚ) : ℝ) * ((97471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c452 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((23379/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1813899/10000000) (δ := 2931/200000000) (ψ := 1326617/1000000) 293 285
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t452 : ((2199015313/62500000000 : ℚ) : ℝ) ≤ stT293 452 := by
  have hc : ((187007/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).1
  have hw2 : ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2199015313/62500000000 : ℚ) : ℝ)
      = ((11759/250000 : ℚ) : ℝ) * ((187007/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c453 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((996957/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -97537/5000000) (δ := 2931/200000000) (ψ := 1326617/1000000) 293 285
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t453 : ((5854541161/125000000000 : ℚ) : ℝ) ≤ stT293 453 := by
  have hc : ((996857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).1
  have hw2 : ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5873/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5854541161/125000000000 : ℚ) : ℝ)
      = ((5873/125000 : ℚ) : ℝ) * ((996857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c454 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((842959/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1420089/10000000) (δ := 29/1953125) (ψ := 1326617/1000000) 293 285
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t454 : ((395573114457/10000000000000 : ℚ) : ℝ) ≤ stT293 454 := by
  have hc : ((842859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).1
  have hw2 : ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((469323/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((395573114457/10000000000000 : ℚ) : ℝ)
      = ((469323/10000000 : ℚ) : ℝ) * ((842859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c455 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((35047/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23686/78125) (δ := 2951/200000000) (ψ := 1326617/1000000) 293 285
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t455 : ((16425590859/1000000000000 : ℚ) : ℝ) ≤ stT293 455 := by
  have hc : ((35037/100000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).1
  have hw2 : ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((468807/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16425590859/1000000000000 : ℚ) : ℝ)
      = ((468807/10000000 : ℚ) : ℝ) * ((35037/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c456 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-281329/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4639939/10000000) (δ := 3687/250000000) (ψ := 1326617/1000000) 293 285
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t456 : ((-131791230697/10000000000000 : ℚ) : ℝ) ≤ stT293 456 := by
  have hc : ((-281429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131791230697/10000000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-281429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c457 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-39991/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9757/15625) (δ := 2931/200000000) (ψ := 1326617/1000000) 293 285
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t457 : ((-4677342219/125000000000 : ℚ) : ℝ) ≤ stT293 457 := by
  have hc : ((-9999/12500 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).2
  have h0 : (0:ℝ) ≤ ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4677342219/125000000000 : ℚ) : ℝ)
      = ((467781/10000000 : ℚ) : ℝ) * ((-9999/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c458 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-499997/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7845579/10000000) (δ := 29/1953125) (ψ := 1326617/1000000) 293 285
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t458 : ((-23365696169/500000000000 : ℚ) : ℝ) ≤ stT293 458 := by
  have hc : ((-500047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).2
  have h0 : (0:ℝ) ≤ ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23365696169/500000000000 : ℚ) : ℝ)
      = ((46727/1000000 : ℚ) : ℝ) * ((-500047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c459 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-50291/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6264729/10000000) (δ := 2931/200000000) (ψ := 1326617/1000000) 293 286
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t459 : ((-93907178829/2500000000000 : ℚ) : ℝ) ≤ stT293 459 := by
  have hc : ((-201189/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).2
  have h0 : (0:ℝ) ≤ ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93907178829/2500000000000 : ℚ) : ℝ)
      = ((466761/10000000 : ℚ) : ℝ) * ((-201189/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c460 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-293101/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4670663/10000000) (δ := 29/1953125) (ψ := 1326617/1000000) 293 286
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t460 : ((-136705845853/10000000000000 : ℚ) : ℝ) ≤ stT293 460 := by
  have hc : ((-293201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).2
  have h0 : (0:ℝ) ≤ ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136705845853/10000000000000 : ℚ) : ℝ)
      = ((466253/10000000 : ℚ) : ℝ) * ((-293201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c461 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((66473/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1539983/5000000) (δ := 29/1953125) (ψ := 1326617/1000000) 293 286
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t461 : ((15475109469/1000000000000 : ℚ) : ℝ) ≤ stT293 461 := by
  have hc : ((66453/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15475109469/1000000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((66453/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c462 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((413481/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -298557/2000000) (δ := 29/1953125) (ψ := 1326617/1000000) 293 286
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t462 : ((96172732651/2500000000000 : ℚ) : ℝ) ≤ stT293 462 := by
  have hc : ((413431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96172732651/2500000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((413431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c463 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((999337/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 91027/10000000) (δ := 2931/200000000) (ψ := 1326617/1000000) 293 286
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t463 : ((464384404143/10000000000000 : ℚ) : ℝ) ≤ stT293 463 := by
  have hc : ((999237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((464384404143/10000000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((999237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c464 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((196179/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 417849/2500000) (δ := 2951/200000000) (ψ := 1326617/1000000) 293 286
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t464 : ((22765535163/625000000000 : ℚ) : ℝ) ≤ stT293 464 := by
  have hc : ((98077/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22765535163/625000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((98077/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c465 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((268117/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 649679/2000000) (δ := 2931/200000000) (ψ := 1326617/1000000) 293 286
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t465 : ((62144833773/5000000000000 : ℚ) : ℝ) ≤ stT293 465 := by
  have hc : ((268017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62144833773/5000000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((268017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c466 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-350387/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4821951/10000000) (δ := 29/1953125) (ψ := 1326617/1000000) 293 286
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t466 : ((-81180149427/5000000000000 : ℚ) : ℝ) ≤ stT293 466 := by
  have hc : ((-350487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).2
  have h0 : (0:ℝ) ≤ ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81180149427/5000000000000 : ℚ) : ℝ)
      = ((231621/5000000 : ℚ) : ℝ) * ((-350487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c467 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-833857/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3196069/5000000) (δ := 29/1953125) (ψ := 1326617/1000000) 293 286
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t467 : ((-77181886393/2000000000000 : ℚ) : ℝ) ≤ stT293 467 := by
  have hc : ((-833957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77181886393/2000000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-833957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c468 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-999119/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7749007/10000000) (δ := 7381/500000000) (ψ := 1326617/1000000) 293 287
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t468 : ((-461889981969/10000000000000 : ℚ) : ℝ) ≤ stT293 468 := by
  have hc : ((-999219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-461889981969/10000000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-999219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c469 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-157087/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3092743/5000000) (δ := 7331/500000000) (ψ := 1326617/1000000) 293 287
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t469 : ((-36272707053/1000000000000 : ℚ) : ℝ) ≤ stT293 469 := by
  have hc : ((-157107/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36272707053/1000000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-157107/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c470 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-275719/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2312667/5000000) (δ := 7381/500000000) (ψ := 1326617/1000000) 293 287
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t470 : ((-63612963427/5000000000000 : ℚ) : ℝ) ≤ stT293 470 := by
  have hc : ((-275819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63612963427/5000000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-275819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c471 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((67339/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3068479/10000000) (δ := 14741/1000000000) (ψ := 1326617/1000000) 293 287
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t471 : ((1240756489/80000000000 : ℚ) : ℝ) ≤ stT293 471 := by
  have hc : ((67319/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).1
  have hw2 : ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18431/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1240756489/80000000000 : ℚ) : ℝ)
      = ((18431/400000 : ℚ) : ℝ) * ((67319/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c472 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((821951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37873/250000) (δ := 14841/1000000000) (ψ := 1326617/1000000) 293 287
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t472 : ((378287331237/10000000000000 : ℚ) : ℝ) ≤ stT293 472 := by
  have hc : ((821851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((378287331237/10000000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((821851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c473 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((9999/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 35343/10000000) (δ := 14841/1000000000) (ψ := 1326617/1000000) 293 287
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t473 : ((11492701/250000000 : ℚ) : ℝ) ≤ stT293 473 := by
  have hc : ((4999/5000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11492701/250000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((4999/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c474 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((201571/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1582383/10000000) (δ := 14841/1000000000) (ψ := 1326617/1000000) 293 287
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t474 : ((9257310099/250000000000 : ℚ) : ℝ) ≤ stT293 474 := by
  have hc : ((100773/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9257310099/250000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((100773/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c475 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((62979/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3126127/10000000) (δ := 14741/1000000000) (ψ := 1326617/1000000) 293 287
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t475 : ((28887540929/2000000000000 : ℚ) : ℝ) ≤ stT293 475 := by
  have hc : ((62959/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28887540929/2000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((62959/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c476 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-291537/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 186663/400000) (δ := 7381/500000000) (ψ := 1326617/1000000) 293 287
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t476 : ((-2673436379/200000000000 : ℚ) : ℝ) ≤ stT293 476 := by
  have hc : ((-291637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).2
  have h0 : (0:ℝ) ≤ ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2673436379/200000000000 : ℚ) : ℝ)
      = ((9167/200000 : ℚ) : ℝ) * ((-291637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c477 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-789947/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6203799/10000000) (δ := 14741/1000000000) (ψ := 1326617/1000000) 293 287
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t477 : ((-361738029843/10000000000000 : ℚ) : ℝ) ≤ stT293 477 := by
  have hc : ((-790047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).2
  have h0 : (0:ℝ) ≤ ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-361738029843/10000000000000 : ℚ) : ℝ)
      = ((457869/10000000 : ℚ) : ℝ) * ((-790047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c478 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-499461/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3868937/5000000) (δ := 7331/500000000) (ψ := 1326617/1000000) 293 287
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t478 : ((-22847133629/500000000000 : ℚ) : ℝ) ≤ stT293 478 := by
  have hc : ((-499511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22847133629/500000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-499511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c479 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-844123/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6439311/10000000) (δ := 7367/500000000) (ψ := 1326617/1000000) 293 288
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t479 : ((-24108476211/625000000000 : ℚ) : ℝ) ≤ stT293 479 := by
  have hc : ((-844223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24108476211/625000000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-844223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c480 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-5996/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4911609/10000000) (δ := 7367/500000000) (ψ := 1326617/1000000) 293 288
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t480 : ((-10950013749/625000000000 : ℚ) : ℝ) ≤ stT293 480 := by
  have hc : ((-95961/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10950013749/625000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-95961/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c481 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((214241/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3387203/10000000) (δ := 14669/1000000000) (ψ := 1326617/1000000) 293 288
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t481 : ((2440993259/250000000000 : ℚ) : ℝ) ≤ stT293 481 := by
  have hc : ((214141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).1
  have hw2 : ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11399/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2440993259/250000000000 : ℚ) : ℝ)
      = ((11399/250000 : ℚ) : ℝ) * ((214141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c482 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((183543/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -932937/5000000) (δ := 7367/500000000) (ψ := 1326617/1000000) 293 288
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t482 : ((41795031633/1250000000000 : ℚ) : ℝ) ≤ stT293 482 := by
  have hc : ((91759/125000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41795031633/1250000000000 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((91759/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c483 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((49517/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43471/1250000) (δ := 7417/500000000) (ψ := 1326617/1000000) 293 288
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t483 : ((563217567/12500000000 : ℚ) : ℝ) ≤ stT293 483 := by
  have hc : ((6189/6250 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((563217567/12500000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((6189/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c484 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((446483/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 583631/5000000) (δ := 7367/500000000) (ψ := 1326617/1000000) 293 288
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t484 : ((40584777597/1000000000000 : ℚ) : ℝ) ≤ stT293 484 := by
  have hc : ((446433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40584777597/1000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((446433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c485 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((59837/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2679069/10000000) (δ := 14669/1000000000) (ψ := 1326617/1000000) 293 288
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t485 : ((13582434831/625000000000 : ℚ) : ℝ) ≤ stT293 485 := by
  have hc : ((119649/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13582434831/625000000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((119649/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c486 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-104163/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 130871/312500) (δ := 7417/500000000) (ψ := 1326617/1000000) 293 288
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t486 : ((-4729473943/1000000000000 : ℚ) : ℝ) ≤ stT293 486 := by
  have hc : ((-104263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).2
  have h0 : (0:ℝ) ≤ ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4729473943/1000000000000 : ℚ) : ℝ)
      = ((45361/1000000 : ℚ) : ℝ) * ((-104263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c487 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-324631/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2846763/5000000) (δ := 7367/500000000) (ψ := 1326617/1000000) 293 288
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t487 : ((-18390905883/625000000000 : ℚ) : ℝ) ≤ stT293 487 := by
  have hc : ((-324681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).2
  have h0 : (0:ℝ) ≤ ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18390905883/625000000000 : ℚ) : ℝ)
      = ((56643/1250000 : ℚ) : ℝ) * ((-324681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c488 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-38623/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7196103/10000000) (δ := 7417/500000000) (ψ := 1326617/1000000) 293 288
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t488 : ((-17485631733/400000000000 : ℚ) : ℝ) ≤ stT293 488 := by
  have hc : ((-38627/40000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17485631733/400000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-38627/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c489 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-943877/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -438277/625000) (δ := 1847/125000000) (ψ := 1326617/1000000) 293 289
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t489 : ((-53360187879/1250000000000 : ℚ) : ℝ) ≤ stT293 489 := by
  have hc : ((-943977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53360187879/1250000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-943977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c490 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-296833/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -689501/1250000) (δ := 3669/250000000) (ψ := 1326617/1000000) 293 289
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t490 : ((-67059041391/2500000000000 : ℚ) : ℝ) ≤ stT293 490 := by
  have hc : ((-296883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67059041391/2500000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-296883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c491 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-38229/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4022587/10000000) (δ := 3669/250000000) (ψ := 1326617/1000000) 293 289
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t491 : ((-8648823863/5000000000000 : ℚ) : ℝ) ≤ stT293 491 := by
  have hc : ((-38329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8648823863/5000000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-38329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c492 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((105881/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2532243/10000000) (δ := 14827/1000000000) (ψ := 1326617/1000000) 293 289
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t492 : ((23862869037/1000000000000 : ℚ) : ℝ) ≤ stT293 492 := by
  have hc : ((105861/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23862869037/1000000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((105861/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c493 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((913907/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41799/400000) (δ := 14827/1000000000) (ψ := 1326617/1000000) 293 289
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t493 : ((411557655239/10000000000000 : ℚ) : ℝ) ≤ stT293 493 := by
  have hc : ((913807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((411557655239/10000000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((913807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c494 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((984597/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 439363/10000000) (δ := 14827/1000000000) (ψ := 1326617/1000000) 293 289
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t494 : ((442945874737/10000000000000 : ℚ) : ℝ) ≤ stT293 494 := by
  have hc : ((984497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((442945874737/10000000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((984497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c495 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((89891/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3073/16000) (δ := 3669/250000000) (ψ := 1326617/1000000) 293 289
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t495 : ((40397329881/1250000000000 : ℚ) : ℝ) ≤ stT293 495 := by
  have hc : ((179757/250000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40397329881/1250000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((179757/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c496 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((209647/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 849739/2500000) (δ := 14827/1000000000) (ψ := 1326617/1000000) 293 289
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t496 : ((94089327111/10000000000000 : ℚ) : ℝ) ≤ stT293 496 := by
  have hc : ((209547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94089327111/10000000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((209547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c497 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-73983/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 974857/2000000) (δ := 1847/125000000) (ψ := 1326617/1000000) 293 289
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t497 : ((-16597466843/1000000000000 : ℚ) : ℝ) ≤ stT293 497 := by
  have hc : ((-74003/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16597466843/1000000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-74003/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c498 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-823667/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 634661/1000000) (δ := 1847/125000000) (ψ := 1326617/1000000) 293 289
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t498 : ((-369139054137/10000000000000 : ℚ) : ℝ) ≤ stT293 498 := by
  have hc : ((-823767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369139054137/10000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-823767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c499 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-199977/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1563201/2000000) (δ := 1847/125000000) (ψ := 1326617/1000000) 293 289
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t499 : ((-44765528507/1000000000000 : ℚ) : ℝ) ≤ stT293 499 := by
  have hc : ((-199997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44765528507/1000000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-199997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_c500 :
    |Real.cos (((293 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-841147/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3212747/5000000) (δ := 14819/1000000000) (ψ := 1326617/1000000) 293 290
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st293_t500 : ((-188108717929/5000000000000 : ℚ) : ℝ) ≤ stT293 500 := by
  have hc : ((-841247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((293 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st293_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).2
  have h0 : (0:ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188108717929/5000000000000 : ℚ) : ℝ)
      = ((223607/5000000 : ℚ) : ℝ) * ((-841247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st293_p1 : ((12083/50000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT293 (i+1) := by
  rw [Finset.sum_range_one]
  exact st293_t1

theorem st293_p2 : ((7807857252413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT293 (i+1))
      = (∑ i ∈ Finset.range 1, stT293 (i+1)) + stT293 2 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 1
    simpa using h
  have hprev := st293_p1
  have hstep := st293_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p3 : ((13536222013777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT293 (i+1))
      = (∑ i ∈ Finset.range 2, stT293 (i+1)) + stT293 3 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 2
    simpa using h
  have hprev := st293_p2
  have hstep := st293_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p4 : ((8945791095691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT293 (i+1))
      = (∑ i ∈ Finset.range 3, stT293 (i+1)) + stT293 4 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 3
    simpa using h
  have hprev := st293_p3
  have hstep := st293_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p5 : ((11360913936821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT293 (i+1))
      = (∑ i ∈ Finset.range 4, stT293 (i+1)) + stT293 5 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 4
    simpa using h
  have hprev := st293_p4
  have hstep := st293_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p6 : ((9110502337833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT293 (i+1))
      = (∑ i ∈ Finset.range 5, stT293 (i+1)) + stT293 6 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 5
    simpa using h
  have hprev := st293_p5
  have hstep := st293_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p7 : ((5403426521833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT293 (i+1))
      = (∑ i ∈ Finset.range 6, stT293 (i+1)) + stT293 7 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 6
    simpa using h
  have hprev := st293_p6
  have hstep := st293_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p8 : ((5585350907881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT293 (i+1))
      = (∑ i ∈ Finset.range 7, stT293 (i+1)) + stT293 8 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 7
    simpa using h
  have hprev := st293_p7
  have hstep := st293_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p9 : ((5570090904829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT293 (i+1))
      = (∑ i ∈ Finset.range 8, stT293 (i+1)) + stT293 9 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 8
    simpa using h
  have hprev := st293_p8
  have hstep := st293_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p10 : ((7197841367809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT293 (i+1))
      = (∑ i ∈ Finset.range 9, stT293 (i+1)) + stT293 10 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 9
    simpa using h
  have hprev := st293_p9
  have hstep := st293_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p11 : ((4855972172869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT293 (i+1))
      = (∑ i ∈ Finset.range 10, stT293 (i+1)) + stT293 11 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 10
    simpa using h
  have hprev := st293_p10
  have hstep := st293_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p12 : ((3402146130629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT293 (i+1))
      = (∑ i ∈ Finset.range 11, stT293 (i+1)) + stT293 12 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 11
    simpa using h
  have hprev := st293_p11
  have hstep := st293_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p13 : ((586232443103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT293 (i+1))
      = (∑ i ∈ Finset.range 12, stT293 (i+1)) + stT293 13 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 12
    simpa using h
  have hprev := st293_p12
  have hstep := st293_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p14 : ((280276355143/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT293 (i+1))
      = (∑ i ∈ Finset.range 13, stT293 (i+1)) + stT293 14 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 13
    simpa using h
  have hprev := st293_p13
  have hstep := st293_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p15 : ((2563298322613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT293 (i+1))
      = (∑ i ∈ Finset.range 14, stT293 (i+1)) + stT293 15 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 14
    simpa using h
  have hprev := st293_p14
  have hstep := st293_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p16 : ((3653504572613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT293 (i+1))
      = (∑ i ∈ Finset.range 15, stT293 (i+1)) + stT293 16 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 15
    simpa using h
  have hprev := st293_p15
  have hstep := st293_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p17 : ((934135895233/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT293 (i+1))
      = (∑ i ∈ Finset.range 16, stT293 (i+1)) + stT293 17 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 16
    simpa using h
  have hprev := st293_p16
  have hstep := st293_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p18 : ((226037053957/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT293 (i+1))
      = (∑ i ∈ Finset.range 17, stT293 (i+1)) + stT293 18 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 17
    simpa using h
  have hprev := st293_p17
  have hstep := st293_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p19 : ((1141187399539/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT293 (i+1))
      = (∑ i ∈ Finset.range 18, stT293 (i+1)) + stT293 19 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 18
    simpa using h
  have hprev := st293_p18
  have hstep := st293_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p20 : ((1725153920699/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT293 (i+1))
      = (∑ i ∈ Finset.range 19, stT293 (i+1)) + stT293 20 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 19
    simpa using h
  have hprev := st293_p19
  have hstep := st293_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p21 : ((14136274247/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT293 (i+1))
      = (∑ i ∈ Finset.range 20, stT293 (i+1)) + stT293 21 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 20
    simpa using h
  have hprev := st293_p20
  have hstep := st293_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p22 : ((9005967321961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT293 (i+1))
      = (∑ i ∈ Finset.range 21, stT293 (i+1)) + stT293 22 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 21
    simpa using h
  have hprev := st293_p21
  have hstep := st293_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p23 : ((11090077090537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT293 (i+1))
      = (∑ i ∈ Finset.range 22, stT293 (i+1)) + stT293 23 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 22
    simpa using h
  have hprev := st293_p22
  have hstep := st293_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p24 : ((3281589979037/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT293 (i+1))
      = (∑ i ∈ Finset.range 23, stT293 (i+1)) + stT293 24 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 23
    simpa using h
  have hprev := st293_p23
  have hstep := st293_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p25 : ((3672271479037/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT293 (i+1))
      = (∑ i ∈ Finset.range 24, stT293 (i+1)) + stT293 25 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 24
    simpa using h
  have hprev := st293_p24
  have hstep := st293_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p26 : ((717111348009/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT293 (i+1))
      = (∑ i ∈ Finset.range 25, stT293 (i+1)) + stT293 26 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 25
    simpa using h
  have hprev := st293_p25
  have hstep := st293_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p27 : ((12430325668227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT293 (i+1))
      = (∑ i ∈ Finset.range 26, stT293 (i+1)) + stT293 27 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 26
    simpa using h
  have hprev := st293_p26
  have hstep := st293_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p28 : ((2652197117879/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT293 (i+1))
      = (∑ i ∈ Finset.range 27, stT293 (i+1)) + stT293 28 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 27
    simpa using h
  have hprev := st293_p27
  have hstep := st293_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p29 : ((13986957650839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT293 (i+1))
      = (∑ i ∈ Finset.range 28, stT293 (i+1)) + stT293 29 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 28
    simpa using h
  have hprev := st293_p28
  have hstep := st293_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p30 : ((12545196579569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT293 (i+1))
      = (∑ i ∈ Finset.range 29, stT293 (i+1)) + stT293 30 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 29
    simpa using h
  have hprev := st293_p29
  have hstep := st293_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p31 : ((14139761169817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT293 (i+1))
      = (∑ i ∈ Finset.range 30, stT293 (i+1)) + stT293 31 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 30
    simpa using h
  have hprev := st293_p30
  have hstep := st293_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p32 : ((12680992770349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT293 (i+1))
      = (∑ i ∈ Finset.range 31, stT293 (i+1)) + stT293 32 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 31
    simpa using h
  have hprev := st293_p31
  have hstep := st293_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p33 : ((13607980361213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT293 (i+1))
      = (∑ i ∈ Finset.range 32, stT293 (i+1)) + stT293 33 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 32
    simpa using h
  have hprev := st293_p32
  have hstep := st293_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p34 : ((13806579054183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT293 (i+1))
      = (∑ i ∈ Finset.range 33, stT293 (i+1)) + stT293 34 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 33
    simpa using h
  have hprev := st293_p33
  have hstep := st293_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p35 : ((12342217038831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT293 (i+1))
      = (∑ i ∈ Finset.range 34, stT293 (i+1)) + stT293 35 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 34
    simpa using h
  have hprev := st293_p34
  have hstep := st293_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p36 : ((13671363173839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT293 (i+1))
      = (∑ i ∈ Finset.range 35, stT293 (i+1)) + stT293 36 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 35
    simpa using h
  have hprev := st293_p35
  have hstep := st293_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p37 : ((14420989278059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT293 (i+1))
      = (∑ i ∈ Finset.range 36, stT293 (i+1)) + stT293 37 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 36
    simpa using h
  have hprev := st293_p36
  have hstep := st293_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p38 : ((6504027306497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT293 (i+1))
      = (∑ i ∈ Finset.range 37, stT293 (i+1)) + stT293 38 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 37
    simpa using h
  have hprev := st293_p37
  have hstep := st293_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p39 : ((5954143865133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT293 (i+1))
      = (∑ i ∈ Finset.range 38, stT293 (i+1)) + stT293 39 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 38
    simpa using h
  have hprev := st293_p38
  have hstep := st293_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p40 : ((3122911753557/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT293 (i+1))
      = (∑ i ∈ Finset.range 39, stT293 (i+1)) + stT293 40 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 39
    simpa using h
  have hprev := st293_p39
  have hstep := st293_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p41 : ((3502017163359/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT293 (i+1))
      = (∑ i ∈ Finset.range 40, stT293 (i+1)) + stT293 41 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 40
    simpa using h
  have hprev := st293_p40
  have hstep := st293_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p42 : ((15334276199309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT293 (i+1))
      = (∑ i ∈ Finset.range 41, stT293 (i+1)) + stT293 42 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 41
    simpa using h
  have hprev := st293_p41
  have hstep := st293_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p43 : ((1995050376953/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT293 (i+1))
      = (∑ i ∈ Finset.range 42, stT293 (i+1)) + stT293 43 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 42
    simpa using h
  have hprev := st293_p42
  have hstep := st293_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p44 : ((3978931264093/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT293 (i+1))
      = (∑ i ∈ Finset.range 43, stT293 (i+1)) + stT293 44 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 43
    simpa using h
  have hprev := st293_p43
  have hstep := st293_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p45 : ((3857818367653/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT293 (i+1))
      = (∑ i ∈ Finset.range 44, stT293 (i+1)) + stT293 45 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 44
    simpa using h
  have hprev := st293_p44
  have hstep := st293_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p46 : ((3685114392583/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT293 (i+1))
      = (∑ i ∈ Finset.range 45, stT293 (i+1)) + stT293 46 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 45
    simpa using h
  have hprev := st293_p45
  have hstep := st293_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p47 : ((7016870093341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT293 (i+1))
      = (∑ i ∈ Finset.range 46, stT293 (i+1)) + stT293 47 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 46
    simpa using h
  have hprev := st293_p46
  have hstep := st293_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p48 : ((1348332029609/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT293 (i+1))
      = (∑ i ∈ Finset.range 47, stT293 (i+1)) + stT293 48 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 47
    simpa using h
  have hprev := st293_p47
  have hstep := st293_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p49 : ((6635285819781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT293 (i+1))
      = (∑ i ∈ Finset.range 48, stT293 (i+1)) + stT293 49 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 48
    simpa using h
  have hprev := st293_p48
  have hstep := st293_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p50 : ((13571299791373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT293 (i+1))
      = (∑ i ∈ Finset.range 49, stT293 (i+1)) + stT293 50 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 49
    simpa using h
  have hprev := st293_p49
  have hstep := st293_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p51 : ((14468319159373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT293 (i+1))
      = (∑ i ∈ Finset.range 50, stT293 (i+1)) + stT293 51 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 50
    simpa using h
  have hprev := st293_p50
  have hstep := st293_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p52 : ((15800268959623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT293 (i+1))
      = (∑ i ∈ Finset.range 51, stT293 (i+1)) + stT293 52 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 51
    simpa using h
  have hprev := st293_p51
  have hstep := st293_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p53 : ((8527077334319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT293 (i+1))
      = (∑ i ∈ Finset.range 52, stT293 (i+1)) + stT293 53 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 52
    simpa using h
  have hprev := st293_p52
  have hstep := st293_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p54 : ((8756507323211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT293 (i+1))
      = (∑ i ∈ Finset.range 53, stT293 (i+1)) + stT293 54 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 53
    simpa using h
  have hprev := st293_p53
  have hstep := st293_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p55 : ((8396682063811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT293 (i+1))
      = (∑ i ∈ Finset.range 54, stT293 (i+1)) + stT293 55 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 54
    simpa using h
  have hprev := st293_p54
  have hstep := st293_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p56 : ((3091387104737/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT293 (i+1))
      = (∑ i ∈ Finset.range 55, stT293 (i+1)) + stT293 56 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 55
    simpa using h
  have hprev := st293_p55
  have hstep := st293_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p57 : ((14847788095117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT293 (i+1))
      = (∑ i ∈ Finset.range 56, stT293 (i+1)) + stT293 57 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 56
    simpa using h
  have hprev := st293_p56
  have hstep := st293_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p58 : ((15703181011789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT293 (i+1))
      = (∑ i ∈ Finset.range 57, stT293 (i+1)) + stT293 58 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 57
    simpa using h
  have hprev := st293_p57
  have hstep := st293_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p59 : ((844764671471/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT293 (i+1))
      = (∑ i ∈ Finset.range 58, stT293 (i+1)) + stT293 59 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 58
    simpa using h
  have hprev := st293_p58
  have hstep := st293_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p60 : ((3327417594889/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT293 (i+1))
      = (∑ i ∈ Finset.range 59, stT293 (i+1)) + stT293 60 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 59
    simpa using h
  have hprev := st293_p59
  have hstep := st293_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p61 : ((7679888887993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT293 (i+1))
      = (∑ i ∈ Finset.range 60, stT293 (i+1)) + stT293 61 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 60
    simpa using h
  have hprev := st293_p60
  have hstep := st293_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p62 : ((15383307084513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT293 (i+1))
      = (∑ i ∈ Finset.range 61, stT293 (i+1)) + stT293 62 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 61
    simpa using h
  have hprev := st293_p61
  have hstep := st293_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p63 : ((16641903005893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT293 (i+1))
      = (∑ i ∈ Finset.range 62, stT293 (i+1)) + stT293 63 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 62
    simpa using h
  have hprev := st293_p62
  have hstep := st293_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p64 : ((2058258326903/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT293 (i+1))
      = (∑ i ∈ Finset.range 63, stT293 (i+1)) + stT293 64 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 63
    simpa using h
  have hprev := st293_p63
  have hstep := st293_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p65 : ((3821245300579/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT293 (i+1))
      = (∑ i ∈ Finset.range 64, stT293 (i+1)) + stT293 65 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 64
    simpa using h
  have hprev := st293_p64
  have hstep := st293_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p66 : ((7963966564167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT293 (i+1))
      = (∑ i ∈ Finset.range 65, stT293 (i+1)) + stT293 66 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 65
    simpa using h
  have hprev := st293_p65
  have hstep := st293_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p67 : ((2091074493351/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT293 (i+1))
      = (∑ i ∈ Finset.range 66, stT293 (i+1)) + stT293 67 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 66
    simpa using h
  have hprev := st293_p66
  have hstep := st293_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p68 : ((15586532457657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT293 (i+1))
      = (∑ i ∈ Finset.range 67, stT293 (i+1)) + stT293 68 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 67
    simpa using h
  have hprev := st293_p67
  have hstep := st293_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p69 : ((627866022111/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT293 (i+1))
      = (∑ i ∈ Finset.range 68, stT293 (i+1)) + stT293 69 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 68
    simpa using h
  have hprev := st293_p68
  have hstep := st293_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p70 : ((16690890207523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT293 (i+1))
      = (∑ i ∈ Finset.range 69, stT293 (i+1)) + stT293 70 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 69
    simpa using h
  have hprev := st293_p69
  have hstep := st293_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p71 : ((3122040354239/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT293 (i+1))
      = (∑ i ∈ Finset.range 70, stT293 (i+1)) + stT293 71 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 70
    simpa using h
  have hprev := st293_p70
  have hstep := st293_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p72 : ((3166093095419/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT293 (i+1))
      = (∑ i ∈ Finset.range 71, stT293 (i+1)) + stT293 72 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 71
    simpa using h
  have hprev := st293_p71
  have hstep := st293_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p73 : ((3318960476129/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT293 (i+1))
      = (∑ i ∈ Finset.range 72, stT293 (i+1)) + stT293 73 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 72
    simpa using h
  have hprev := st293_p72
  have hstep := st293_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p74 : ((7716163271561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT293 (i+1))
      = (∑ i ∈ Finset.range 73, stT293 (i+1)) + stT293 74 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 73
    simpa using h
  have hprev := st293_p73
  have hstep := st293_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p75 : ((8127701238311/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT293 (i+1))
      = (∑ i ∈ Finset.range 74, stT293 (i+1)) + stT293 75 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 74
    simpa using h
  have hprev := st293_p74
  have hstep := st293_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p76 : ((4048234859189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT293 (i+1))
      = (∑ i ∈ Finset.range 75, stT293 (i+1)) + stT293 76 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 75
    simpa using h
  have hprev := st293_p75
  have hstep := st293_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p77 : ((1939701969849/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT293 (i+1))
      = (∑ i ∈ Finset.range 76, stT293 (i+1)) + stT293 77 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 76
    simpa using h
  have hprev := st293_p76
  have hstep := st293_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p78 : ((518750852491/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT293 (i+1))
      = (∑ i ∈ Finset.range 77, stT293 (i+1)) + stT293 78 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 77
    simpa using h
  have hprev := st293_p77
  have hstep := st293_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p79 : ((485090750979/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT293 (i+1))
      = (∑ i ∈ Finset.range 78, stT293 (i+1)) + stT293 79 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 78
    simpa using h
  have hprev := st293_p78
  have hstep := st293_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p80 : ((16271209108393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT293 (i+1))
      = (∑ i ∈ Finset.range 79, stT293 (i+1)) + stT293 80 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 79
    simpa using h
  have hprev := st293_p79
  have hstep := st293_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p81 : ((16012158901153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT293 (i+1))
      = (∑ i ∈ Finset.range 80, stT293 (i+1)) + stT293 81 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 80
    simpa using h
  have hprev := st293_p80
  have hstep := st293_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p82 : ((630913791577/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT293 (i+1))
      = (∑ i ∈ Finset.range 81, stT293 (i+1)) + stT293 82 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 81
    simpa using h
  have hprev := st293_p81
  have hstep := st293_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p83 : ((16417910332911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT293 (i+1))
      = (∑ i ∈ Finset.range 82, stT293 (i+1)) + stT293 83 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 82
    simpa using h
  have hprev := st293_p82
  have hstep := st293_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p84 : ((15502203230601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT293 (i+1))
      = (∑ i ∈ Finset.range 83, stT293 (i+1)) + stT293 84 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 83
    simpa using h
  have hprev := st293_p83
  have hstep := st293_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p85 : ((16553252711641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT293 (i+1))
      = (∑ i ∈ Finset.range 84, stT293 (i+1)) + stT293 85 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 84
    simpa using h
  have hprev := st293_p84
  have hstep := st293_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p86 : ((15475522105353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT293 (i+1))
      = (∑ i ∈ Finset.range 85, stT293 (i+1)) + stT293 86 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 85
    simpa using h
  have hprev := st293_p85
  have hstep := st293_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p87 : ((3301040196901/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT293 (i+1))
      = (∑ i ∈ Finset.range 86, stT293 (i+1)) + stT293 87 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 86
    simpa using h
  have hprev := st293_p86
  have hstep := st293_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p88 : ((3112798814557/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT293 (i+1))
      = (∑ i ∈ Finset.range 87, stT293 (i+1)) + stT293 88 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 87
    simpa using h
  have hprev := st293_p87
  have hstep := st293_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p89 : ((8201253939813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT293 (i+1))
      = (∑ i ∈ Finset.range 88, stT293 (i+1)) + stT293 89 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 88
    simpa using h
  have hprev := st293_p88
  have hstep := st293_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p90 : ((7830350235903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT293 (i+1))
      = (∑ i ∈ Finset.range 89, stT293 (i+1)) + stT293 90 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 89
    simpa using h
  have hprev := st293_p89
  have hstep := st293_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p91 : ((1632340569921/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT293 (i+1))
      = (∑ i ∈ Finset.range 90, stT293 (i+1)) + stT293 91 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 90
    simpa using h
  have hprev := st293_p90
  have hstep := st293_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p92 : ((3142849186781/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT293 (i+1))
      = (∑ i ∈ Finset.range 91, stT293 (i+1)) + stT293 92 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 91
    simpa using h
  have hprev := st293_p91
  have hstep := st293_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p93 : ((8148914238171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT293 (i+1))
      = (∑ i ∈ Finset.range 92, stT293 (i+1)) + stT293 93 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 92
    simpa using h
  have hprev := st293_p92
  have hstep := st293_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p94 : ((7855230232157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT293 (i+1))
      = (∑ i ∈ Finset.range 93, stT293 (i+1)) + stT293 94 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 93
    simpa using h
  have hprev := st293_p93
  have hstep := st293_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p95 : ((4082158438713/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT293 (i+1))
      = (∑ i ∈ Finset.range 94, stT293 (i+1)) + stT293 95 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 94
    simpa using h
  have hprev := st293_p94
  have hstep := st293_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p96 : ((7827666061197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT293 (i+1))
      = (∑ i ∈ Finset.range 95, stT293 (i+1)) + stT293 96 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 95
    simpa using h
  have hprev := st293_p95
  have hstep := st293_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p97 : ((8200723473171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT293 (i+1))
      = (∑ i ∈ Finset.range 96, stT293 (i+1)) + stT293 97 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 96
    simpa using h
  have hprev := st293_p96
  have hstep := st293_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p98 : ((15572671968257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT293 (i+1))
      = (∑ i ∈ Finset.range 97, stT293 (i+1)) + stT293 98 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 97
    simpa using h
  have hprev := st293_p97
  have hstep := st293_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p99 : ((8240544868131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT293 (i+1))
      = (∑ i ∈ Finset.range 98, stT293 (i+1)) + stT293 99 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 98
    simpa using h
  have hprev := st293_p98
  have hstep := st293_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p100 : ((7755424868131/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT293 (i+1))
      = (∑ i ∈ Finset.range 99, stT293 (i+1)) + stT293 100 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 99
    simpa using h
  have hprev := st293_p99
  have hstep := st293_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p101 : ((2063201264497/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT293 (i+1))
      = (∑ i ∈ Finset.range 100, stT293 (i+1)) + stT293 101 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 100
    simpa using h
  have hprev := st293_p100
  have hstep := st293_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p102 : ((1942851250467/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT293 (i+1))
      = (∑ i ∈ Finset.range 101, stT293 (i+1)) + stT293 102 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 101
    simpa using h
  have hprev := st293_p101
  have hstep := st293_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p103 : ((16398257861601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT293 (i+1))
      = (∑ i ∈ Finset.range 102, stT293 (i+1)) + stT293 103 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 102
    simpa using h
  have hprev := st293_p102
  have hstep := st293_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p104 : ((3934046069779/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT293 (i+1))
      = (∑ i ∈ Finset.range 103, stT293 (i+1)) + stT293 104 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 103
    simpa using h
  have hprev := st293_p103
  have hstep := st293_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p105 : ((4029782347729/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT293 (i+1))
      = (∑ i ∈ Finset.range 104, stT293 (i+1)) + stT293 105 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 104
    simpa using h
  have hprev := st293_p104
  have hstep := st293_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p106 : ((8040572654657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT293 (i+1))
      = (∑ i ∈ Finset.range 105, stT293 (i+1)) + stT293 106 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 105
    simpa using h
  have hprev := st293_p105
  have hstep := st293_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p107 : ((15748318061691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT293 (i+1))
      = (∑ i ∈ Finset.range 106, stT293 (i+1)) + stT293 107 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 106
    simpa using h
  have hprev := st293_p106
  have hstep := st293_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p108 : ((16416247540941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT293 (i+1))
      = (∑ i ∈ Finset.range 107, stT293 (i+1)) + stT293 108 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 107
    simpa using h
  have hprev := st293_p107
  have hstep := st293_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p109 : ((3880126961227/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT293 (i+1))
      = (∑ i ∈ Finset.range 108, stT293 (i+1)) + stT293 109 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 108
    simpa using h
  have hprev := st293_p108
  have hstep := st293_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p110 : ((8234388168697/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT293 (i+1))
      = (∑ i ∈ Finset.range 109, stT293 (i+1)) + stT293 110 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 109
    simpa using h
  have hprev := st293_p109
  have hstep := st293_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p111 : ((1568180286317/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT293 (i+1))
      = (∑ i ∈ Finset.range 110, stT293 (i+1)) + stT293 111 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 110
    simpa using h
  have hprev := st293_p110
  have hstep := st293_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p112 : ((8052111717949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT293 (i+1))
      = (∑ i ∈ Finset.range 111, stT293 (i+1)) + stT293 112 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 111
    simpa using h
  have hprev := st293_p111
  have hstep := st293_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p113 : ((8086623912589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT293 (i+1))
      = (∑ i ∈ Finset.range 112, stT293 (i+1)) + stT293 113 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 112
    simpa using h
  have hprev := st293_p112
  have hstep := st293_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p114 : ((7809313910193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT293 (i+1))
      = (∑ i ∈ Finset.range 113, stT293 (i+1)) + stT293 114 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 113
    simpa using h
  have hprev := st293_p113
  have hstep := st293_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p115 : ((8246519809349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT293 (i+1))
      = (∑ i ∈ Finset.range 114, stT293 (i+1)) + stT293 115 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 114
    simpa using h
  have hprev := st293_p114
  have hstep := st293_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p116 : ((15593390901071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT293 (i+1))
      = (∑ i ∈ Finset.range 115, stT293 (i+1)) + stT293 116 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 115
    simpa using h
  have hprev := st293_p115
  have hstep := st293_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p117 : ((16184629914571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT293 (i+1))
      = (∑ i ∈ Finset.range 116, stT293 (i+1)) + stT293 117 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 116
    simpa using h
  have hprev := st293_p116
  have hstep := st293_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p118 : ((8071079593473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT293 (i+1))
      = (∑ i ∈ Finset.range 117, stT293 (i+1)) + stT293 118 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 117
    simpa using h
  have hprev := st293_p117
  have hstep := st293_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p119 : ((7803608826049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT293 (i+1))
      = (∑ i ∈ Finset.range 118, stT293 (i+1)) + stT293 119 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 118
    simpa using h
  have hprev := st293_p118
  have hstep := st293_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p120 : ((8244874665259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT293 (i+1))
      = (∑ i ∈ Finset.range 119, stT293 (i+1)) + stT293 120 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 119
    simpa using h
  have hprev := st293_p119
  have hstep := st293_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p121 : ((783591189709/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT293 (i+1))
      = (∑ i ∈ Finset.range 120, stT293 (i+1)) + stT293 121 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 120
    simpa using h
  have hprev := st293_p120
  have hstep := st293_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p122 : ((8007483386089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT293 (i+1))
      = (∑ i ∈ Finset.range 121, stT293 (i+1)) + stT293 122 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 121
    simpa using h
  have hprev := st293_p121
  have hstep := st293_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p123 : ((3266655333513/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT293 (i+1))
      = (∑ i ∈ Finset.range 122, stT293 (i+1)) + stT293 123 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 122
    simpa using h
  have hprev := st293_p122
  have hstep := st293_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p124 : ((7760496193749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT293 (i+1))
      = (∑ i ∈ Finset.range 123, stT293 (i+1)) + stT293 124 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 123
    simpa using h
  have hprev := st293_p123
  have hstep := st293_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p125 : ((16361903136807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT293 (i+1))
      = (∑ i ∈ Finset.range 124, stT293 (i+1)) + stT293 125 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 124
    simpa using h
  have hprev := st293_p124
  have hstep := st293_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p126 : ((16001397932721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT293 (i+1))
      = (∑ i ∈ Finset.range 125, stT293 (i+1)) + stT293 126 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 125
    simpa using h
  have hprev := st293_p125
  have hstep := st293_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p127 : ((7824250245303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT293 (i+1))
      = (∑ i ∈ Finset.range 126, stT293 (i+1)) + stT293 127 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 126
    simpa using h
  have hprev := st293_p126
  have hstep := st293_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p128 : ((1648787821379/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT293 (i+1))
      = (∑ i ∈ Finset.range 127, stT293 (i+1)) + stT293 128 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 127
    simpa using h
  have hprev := st293_p127
  have hstep := st293_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p129 : ((15733999969099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT293 (i+1))
      = (∑ i ∈ Finset.range 128, stT293 (i+1)) + stT293 129 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 128
    simpa using h
  have hprev := st293_p128
  have hstep := st293_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p130 : ((15863858053637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT293 (i+1))
      = (∑ i ∈ Finset.range 129, stT293 (i+1)) + stT293 130 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 129
    simpa using h
  have hprev := st293_p129
  have hstep := st293_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p131 : ((16457820380621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT293 (i+1))
      = (∑ i ∈ Finset.range 130, stT293 (i+1)) + stT293 131 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 130
    simpa using h
  have hprev := st293_p130
  have hstep := st293_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p132 : ((243607674639/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT293 (i+1))
      = (∑ i ∈ Finset.range 131, stT293 (i+1)) + stT293 132 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 131
    simpa using h
  have hprev := st293_p131
  have hstep := st293_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p133 : ((501381309011/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT293 (i+1))
      = (∑ i ∈ Finset.range 132, stT293 (i+1)) + stT293 133 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 132
    simpa using h
  have hprev := st293_p132
  have hstep := st293_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p134 : ((81889078079/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT293 (i+1))
      = (∑ i ∈ Finset.range 133, stT293 (i+1)) + stT293 134 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 133
    simpa using h
  have hprev := st293_p133
  have hstep := st293_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p135 : ((15536162079481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT293 (i+1))
      = (∑ i ∈ Finset.range 134, stT293 (i+1)) + stT293 135 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 134
    simpa using h
  have hprev := st293_p134
  have hstep := st293_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p136 : ((16152763996873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT293 (i+1))
      = (∑ i ∈ Finset.range 135, stT293 (i+1)) + stT293 136 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 135
    simpa using h
  have hprev := st293_p135
  have hstep := st293_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p137 : ((8158035032819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT293 (i+1))
      = (∑ i ∈ Finset.range 136, stT293 (i+1)) + stT293 137 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 136
    simpa using h
  have hprev := st293_p136
  have hstep := st293_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p138 : ((3880405212569/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT293 (i+1))
      = (∑ i ∈ Finset.range 137, stT293 (i+1)) + stT293 138 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 137
    simpa using h
  have hprev := st293_p137
  have hstep := st293_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p139 : ((4048111064399/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT293 (i+1))
      = (∑ i ∈ Finset.range 138, stT293 (i+1)) + stT293 139 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 138
    simpa using h
  have hprev := st293_p138
  have hstep := st293_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p140 : ((1630091216711/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT293 (i+1))
      = (∑ i ∈ Finset.range 139, stT293 (i+1)) + stT293 140 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 139
    simpa using h
  have hprev := st293_p139
  have hstep := st293_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p141 : ((1552057833467/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT293 (i+1))
      = (∑ i ∈ Finset.range 140, stT293 (i+1)) + stT293 141 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 140
    simpa using h
  have hprev := st293_p140
  have hstep := st293_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p142 : ((2021290117171/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT293 (i+1))
      = (∑ i ∈ Finset.range 141, stT293 (i+1)) + stT293 142 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 141
    simpa using h
  have hprev := st293_p141
  have hstep := st293_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p143 : ((1633615692463/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT293 (i+1))
      = (∑ i ∈ Finset.range 142, stT293 (i+1)) + stT293 143 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 142
    simpa using h
  have hprev := st293_p142
  have hstep := st293_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p144 : ((7766606474471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT293 (i+1))
      = (∑ i ∈ Finset.range 143, stT293 (i+1)) + stT293 144 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 143
    simpa using h
  have hprev := st293_p143
  have hstep := st293_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p145 : ((8042902672541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT293 (i+1))
      = (∑ i ∈ Finset.range 144, stT293 (i+1)) + stT293 145 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 144
    simpa using h
  have hprev := st293_p144
  have hstep := st293_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p146 : ((4101936336323/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT293 (i+1))
      = (∑ i ∈ Finset.range 145, stT293 (i+1)) + stT293 146 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 145
    simpa using h
  have hprev := st293_p145
  have hstep := st293_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p147 : ((3895808868431/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT293 (i+1))
      = (∑ i ∈ Finset.range 146, stT293 (i+1)) + stT293 147 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 146
    simpa using h
  have hprev := st293_p146
  have hstep := st293_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p148 : ((7968564686269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT293 (i+1))
      = (∑ i ∈ Finset.range 147, stT293 (i+1)) + stT293 148 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 147
    simpa using h
  have hprev := st293_p147
  have hstep := st293_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p149 : ((16479271052177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT293 (i+1))
      = (∑ i ∈ Finset.range 148, stT293 (i+1)) + stT293 149 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 148
    simpa using h
  have hprev := st293_p148
  have hstep := st293_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p150 : ((15707882245439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT293 (i+1))
      = (∑ i ∈ Finset.range 149, stT293 (i+1)) + stT293 150 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 149
    simpa using h
  have hprev := st293_p149
  have hstep := st293_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p151 : ((15741818018827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT293 (i+1))
      = (∑ i ∈ Finset.range 150, stT293 (i+1)) + stT293 151 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 150
    simpa using h
  have hprev := st293_p150
  have hstep := st293_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p152 : ((3297444097037/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT293 (i+1))
      = (∑ i ∈ Finset.range 151, stT293 (i+1)) + stT293 152 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 151
    simpa using h
  have hprev := st293_p151
  have hstep := st293_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p153 : ((796639777229/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT293 (i+1))
      = (∑ i ∈ Finset.range 152, stT293 (i+1)) + stT293 153 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 152
    simpa using h
  have hprev := st293_p152
  have hstep := st293_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p154 : ((1556257628369/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT293 (i+1))
      = (∑ i ∈ Finset.range 153, stT293 (i+1)) + stT293 154 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 153
    simpa using h
  have hprev := st293_p153
  have hstep := st293_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p155 : ((16356502843079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT293 (i+1))
      = (∑ i ∈ Finset.range 154, stT293 (i+1)) + stT293 155 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 154
    simpa using h
  have hprev := st293_p154
  have hstep := st293_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p156 : ((16227394677983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT293 (i+1))
      = (∑ i ∈ Finset.range 155, stT293 (i+1)) + stT293 156 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 155
    simpa using h
  have hprev := st293_p155
  have hstep := st293_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p157 : ((3878337956423/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT293 (i+1))
      = (∑ i ∈ Finset.range 156, stT293 (i+1)) + stT293 157 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 156
    simpa using h
  have hprev := st293_p156
  have hstep := st293_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p158 : ((8028590135433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT293 (i+1))
      = (∑ i ∈ Finset.range 157, stT293 (i+1)) + stT293 158 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 157
    simpa using h
  have hprev := st293_p157
  have hstep := st293_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p159 : ((8232486719737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT293 (i+1))
      = (∑ i ∈ Finset.range 158, stT293 (i+1)) + stT293 159 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 158
    simpa using h
  have hprev := st293_p158
  have hstep := st293_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p160 : ((3925954149081/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT293 (i+1))
      = (∑ i ∈ Finset.range 159, stT293 (i+1)) + stT293 160 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 159
    simpa using h
  have hprev := st293_p159
  have hstep := st293_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p161 : ((15688556403031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT293 (i+1))
      = (∑ i ∈ Finset.range 160, stT293 (i+1)) + stT293 161 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 160
    simpa using h
  have hprev := st293_p160
  have hstep := st293_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p162 : ((16454488772433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT293 (i+1))
      = (∑ i ∈ Finset.range 161, stT293 (i+1)) + stT293 162 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 161
    simpa using h
  have hprev := st293_p161
  have hstep := st293_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p163 : ((16109147431011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT293 (i+1))
      = (∑ i ∈ Finset.range 162, stT293 (i+1)) + stT293 163 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 162
    simpa using h
  have hprev := st293_p162
  have hstep := st293_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p164 : ((15500780201801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT293 (i+1))
      = (∑ i ∈ Finset.range 163, stT293 (i+1)) + stT293 164 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 163
    simpa using h
  have hprev := st293_p163
  have hstep := st293_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p165 : ((16104715595261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT293 (i+1))
      = (∑ i ∈ Finset.range 164, stT293 (i+1)) + stT293 165 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 164
    simpa using h
  have hprev := st293_p164
  have hstep := st293_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p166 : ((16465184492061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT293 (i+1))
      = (∑ i ∈ Finset.range 165, stT293 (i+1)) + stT293 166 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 165
    simpa using h
  have hprev := st293_p165
  have hstep := st293_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p167 : ((3144902377209/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT293 (i+1))
      = (∑ i ∈ Finset.range 166, stT293 (i+1)) + stT293 167 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 166
    simpa using h
  have hprev := st293_p166
  have hstep := st293_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p168 : ((15635390871307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT293 (i+1))
      = (∑ i ∈ Finset.range 167, stT293 (i+1)) + stT293 168 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 167
    simpa using h
  have hprev := st293_p167
  have hstep := st293_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p169 : ((16403487026287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT293 (i+1))
      = (∑ i ∈ Finset.range 168, stT293 (i+1)) + stT293 169 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 168
    simpa using h
  have hprev := st293_p168
  have hstep := st293_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p170 : ((4060836375313/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT293 (i+1))
      = (∑ i ∈ Finset.range 169, stT293 (i+1)) + stT293 170 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 169
    simpa using h
  have hprev := st293_p169
  have hstep := st293_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p171 : ((3881752907453/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT293 (i+1))
      = (∑ i ∈ Finset.range 170, stT293 (i+1)) + stT293 171 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 170
    simpa using h
  have hprev := st293_p170
  have hstep := st293_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p172 : ((3972383087819/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT293 (i+1))
      = (∑ i ∈ Finset.range 171, stT293 (i+1)) + stT293 172 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 171
    simpa using h
  have hprev := st293_p171
  have hstep := st293_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p173 : ((16506759844821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT293 (i+1))
      = (∑ i ∈ Finset.range 172, stT293 (i+1)) + stT293 173 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 172
    simpa using h
  have hprev := st293_p172
  have hstep := st293_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p174 : ((15994779201369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT293 (i+1))
      = (∑ i ∈ Finset.range 173, stT293 (i+1)) + stT293 174 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 173
    simpa using h
  have hprev := st293_p173
  have hstep := st293_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p175 : ((15495575784633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT293 (i+1))
      = (∑ i ∈ Finset.range 174, stT293 (i+1)) + stT293 175 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 174
    simpa using h
  have hprev := st293_p174
  have hstep := st293_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p176 : ((16107896790041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT293 (i+1))
      = (∑ i ∈ Finset.range 175, stT293 (i+1)) + stT293 176 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 175
    simpa using h
  have hprev := st293_p175
  have hstep := st293_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p177 : ((16489874267489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT293 (i+1))
      = (∑ i ∈ Finset.range 176, stT293 (i+1)) + stT293 177 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 176
    simpa using h
  have hprev := st293_p176
  have hstep := st293_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p178 : ((3163192210381/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT293 (i+1))
      = (∑ i ∈ Finset.range 177, stT293 (i+1)) + stT293 178 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 177
    simpa using h
  have hprev := st293_p177
  have hstep := st293_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p179 : ((15536835562321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT293 (i+1))
      = (∑ i ∈ Finset.range 178, stT293 (i+1)) + stT293 179 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 178
    simpa using h
  have hprev := st293_p178
  have hstep := st293_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p180 : ((8122009348353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT293 (i+1))
      = (∑ i ∈ Finset.range 179, stT293 (i+1)) + stT293 180 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 179
    simpa using h
  have hprev := st293_p179
  have hstep := st293_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p181 : ((4110304206197/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT293 (i+1))
      = (∑ i ∈ Finset.range 180, stT293 (i+1)) + stT293 181 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 180
    simpa using h
  have hprev := st293_p180
  have hstep := st293_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p182 : ((7859296848019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT293 (i+1))
      = (∑ i ∈ Finset.range 181, stT293 (i+1)) + stT293 182 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 181
    simpa using h
  have hprev := st293_p181
  have hstep := st293_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p183 : ((7789307309059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT293 (i+1))
      = (∑ i ∈ Finset.range 182, stT293 (i+1)) + stT293 183 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 182
    simpa using h
  have hprev := st293_p182
  have hstep := st293_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p184 : ((16305801261763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT293 (i+1))
      = (∑ i ∈ Finset.range 183, stT293 (i+1)) + stT293 184 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 183
    simpa using h
  have hprev := st293_p183
  have hstep := st293_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p185 : ((3282709080607/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT293 (i+1))
      = (∑ i ∈ Finset.range 184, stT293 (i+1)) + stT293 185 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 184
    simpa using h
  have hprev := st293_p184
  have hstep := st293_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p186 : ((15687254614427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT293 (i+1))
      = (∑ i ∈ Finset.range 185, stT293 (i+1)) + stT293 186 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 185
    simpa using h
  have hprev := st293_p185
  have hstep := st293_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p187 : ((15586439856101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT293 (i+1))
      = (∑ i ∈ Finset.range 186, stT293 (i+1)) + stT293 187 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 186
    simpa using h
  have hprev := st293_p186
  have hstep := st293_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p188 : ((3261579035893/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT293 (i+1))
      = (∑ i ∈ Finset.range 187, stT293 (i+1)) + stT293 188 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 187
    simpa using h
  have hprev := st293_p187
  have hstep := st293_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p189 : ((3285135625813/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT293 (i+1))
      = (∑ i ∈ Finset.range 188, stT293 (i+1)) + stT293 189 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 188
    simpa using h
  have hprev := st293_p188
  have hstep := st293_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p190 : ((15712827330773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT293 (i+1))
      = (∑ i ∈ Finset.range 189, stT293 (i+1)) + stT293 190 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 189
    simpa using h
  have hprev := st293_p189
  have hstep := st293_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p191 : ((1944347376781/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT293 (i+1))
      = (∑ i ∈ Finset.range 190, stT293 (i+1)) + stT293 191 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 190
    simpa using h
  have hprev := st293_p190
  have hstep := st293_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p192 : ((16251974122529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT293 (i+1))
      = (∑ i ∈ Finset.range 191, stT293 (i+1)) + stT293 192 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 191
    simpa using h
  have hprev := st293_p191
  have hstep := st293_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p193 : ((2058901651973/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT293 (i+1))
      = (∑ i ∈ Finset.range 192, stT293 (i+1)) + stT293 193 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 192
    simpa using h
  have hprev := st293_p192
  have hstep := st293_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p194 : ((15800779511789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT293 (i+1))
      = (∑ i ∈ Finset.range 193, stT293 (i+1)) + stT293 194 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 193
    simpa using h
  have hprev := st293_p193
  have hstep := st293_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p195 : ((15501830143889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT293 (i+1))
      = (∑ i ∈ Finset.range 194, stT293 (i+1)) + stT293 195 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 194
    simpa using h
  have hprev := st293_p194
  have hstep := st293_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p196 : ((16127706660869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT293 (i+1))
      = (∑ i ∈ Finset.range 195, stT293 (i+1)) + stT293 196 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 195
    simpa using h
  have hprev := st293_p195
  have hstep := st293_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p197 : ((16519456152959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT293 (i+1))
      = (∑ i ∈ Finset.range 196, stT293 (i+1)) + stT293 197 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 196
    simpa using h
  have hprev := st293_p196
  have hstep := st293_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p198 : ((15962148028289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT293 (i+1))
      = (∑ i ∈ Finset.range 197, stT293 (i+1)) + stT293 198 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 197
    simpa using h
  have hprev := st293_p197
  have hstep := st293_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p199 : ((15471522998387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT293 (i+1))
      = (∑ i ∈ Finset.range 198, stT293 (i+1)) + stT293 199 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 198
    simpa using h
  have hprev := st293_p198
  have hstep := st293_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p200 : ((15929353627313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT293 (i+1))
      = (∑ i ∈ Finset.range 199, stT293 (i+1)) + stT293 200 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 199
    simpa using h
  have hprev := st293_p199
  have hstep := st293_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p201 : ((16513428661463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT293 (i+1))
      = (∑ i ∈ Finset.range 200, stT293 (i+1)) + stT293 201 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 200
    simpa using h
  have hprev := st293_p200
  have hstep := st293_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p202 : ((16189551948093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT293 (i+1))
      = (∑ i ∈ Finset.range 201, stT293 (i+1)) + stT293 202 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 201
    simpa using h
  have hprev := st293_p201
  have hstep := st293_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p203 : ((15531226913709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT293 (i+1))
      = (∑ i ∈ Finset.range 202, stT293 (i+1)) + stT293 203 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 202
    simpa using h
  have hprev := st293_p202
  have hstep := st293_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p204 : ((15686249111949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT293 (i+1))
      = (∑ i ∈ Finset.range 203, stT293 (i+1)) + stT293 204 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 203
    simpa using h
  have hprev := st293_p203
  have hstep := st293_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p205 : ((16382067682179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT293 (i+1))
      = (∑ i ∈ Finset.range 204, stT293 (i+1)) + stT293 205 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 204
    simpa using h
  have hprev := st293_p204
  have hstep := st293_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p206 : ((3284707724761/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT293 (i+1))
      = (∑ i ∈ Finset.range 205, stT293 (i+1)) + stT293 206 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 205
    simpa using h
  have hprev := st293_p205
  have hstep := st293_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p207 : ((15743918321507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT293 (i+1))
      = (∑ i ∈ Finset.range 206, stT293 (i+1)) + stT293 207 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 206
    simpa using h
  have hprev := st293_p206
  have hstep := st293_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p208 : ((15492910662499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT293 (i+1))
      = (∑ i ∈ Finset.range 207, stT293 (i+1)) + stT293 208 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 207
    simpa using h
  have hprev := st293_p207
  have hstep := st293_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p209 : ((3217522216457/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT293 (i+1))
      = (∑ i ∈ Finset.range 208, stT293 (i+1)) + stT293 209 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 208
    simpa using h
  have hprev := st293_p208
  have hstep := st293_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p210 : ((3307264893681/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT293 (i+1))
      = (∑ i ∈ Finset.range 209, stT293 (i+1)) + stT293 210 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 209
    simpa using h
  have hprev := st293_p209
  have hstep := st293_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p211 : ((16101300675873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT293 (i+1))
      = (∑ i ∈ Finset.range 210, stT293 (i+1)) + stT293 211 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 210
    simpa using h
  have hprev := st293_p210
  have hstep := st293_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p212 : ((3874496533839/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT293 (i+1))
      = (∑ i ∈ Finset.range 211, stT293 (i+1)) + stT293 212 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 211
    simpa using h
  have hprev := st293_p211
  have hstep := st293_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p213 : ((785231188101/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT293 (i+1))
      = (∑ i ∈ Finset.range 212, stT293 (i+1)) + stT293 213 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 212
    simpa using h
  have hprev := st293_p212
  have hstep := st293_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p214 : ((3276830883877/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT293 (i+1))
      = (∑ i ∈ Finset.range 213, stT293 (i+1)) + stT293 214 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 213
    simpa using h
  have hprev := st293_p213
  have hstep := st293_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p215 : ((3289998824029/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT293 (i+1))
      = (∑ i ∈ Finset.range 214, stT293 (i+1)) + stT293 215 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 214
    simpa using h
  have hprev := st293_p214
  have hstep := st293_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p216 : ((15801520794547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT293 (i+1))
      = (∑ i ∈ Finset.range 215, stT293 (i+1)) + stT293 216 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 215
    simpa using h
  have hprev := st293_p215
  have hstep := st293_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p217 : ((3865241664983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT293 (i+1))
      = (∑ i ∈ Finset.range 216, stT293 (i+1)) + stT293 217 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 216
    simpa using h
  have hprev := st293_p216
  have hstep := st293_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p218 : ((3989221393373/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT293 (i+1))
      = (∑ i ∈ Finset.range 217, stT293 (i+1)) + stT293 218 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 217
    simpa using h
  have hprev := st293_p217
  have hstep := st293_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p219 : ((8258801337887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT293 (i+1))
      = (∑ i ∈ Finset.range 218, stT293 (i+1)) + stT293 219 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 218
    simpa using h
  have hprev := st293_p218
  have hstep := st293_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p220 : ((8141295694087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT293 (i+1))
      = (∑ i ∈ Finset.range 219, stT293 (i+1)) + stT293 220 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 219
    simpa using h
  have hprev := st293_p219
  have hstep := st293_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p221 : ((24982743601/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT293 (i+1))
      = (∑ i ∈ Finset.range 220, stT293 (i+1)) + stT293 221 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 220
    simpa using h
  have hprev := st293_p220
  have hstep := st293_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p222 : ((3881111372101/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT293 (i+1))
      = (∑ i ∈ Finset.range 221, stT293 (i+1)) + stT293 222 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 221
    simpa using h
  have hprev := st293_p221
  have hstep := st293_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p223 : ((16144253182983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT293 (i+1))
      = (∑ i ∈ Finset.range 222, stT293 (i+1)) + stT293 223 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 222
    simpa using h
  have hprev := st293_p222
  have hstep := st293_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p224 : ((16547381959227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT293 (i+1))
      = (∑ i ∈ Finset.range 223, stT293 (i+1)) + stT293 224 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 223
    simpa using h
  have hprev := st293_p223
  have hstep := st293_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p225 : ((16139983088861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT293 (i+1))
      = (∑ i ∈ Finset.range 224, stT293 (i+1)) + stT293 225 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 224
    simpa using h
  have hprev := st293_p224
  have hstep := st293_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p226 : ((15523630412081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT293 (i+1))
      = (∑ i ∈ Finset.range 225, stT293 (i+1)) + stT293 226 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 225
    simpa using h
  have hprev := st293_p225
  have hstep := st293_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p227 : ((7797771403981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT293 (i+1))
      = (∑ i ∈ Finset.range 226, stT293 (i+1)) + stT293 227 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 226
    simpa using h
  have hprev := st293_p226
  have hstep := st293_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p228 : ((4061929134097/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT293 (i+1))
      = (∑ i ∈ Finset.range 227, stT293 (i+1)) + stT293 228 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 227
    simpa using h
  have hprev := st293_p227
  have hstep := st293_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p229 : ((2067829786019/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT293 (i+1))
      = (∑ i ∈ Finset.range 228, stT293 (i+1)) + stT293 229 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 228
    simpa using h
  have hprev := st293_p228
  have hstep := st293_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p230 : ((4015799272001/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT293 (i+1))
      = (∑ i ∈ Finset.range 229, stT293 (i+1)) + stT293 230 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 229
    simpa using h
  have hprev := st293_p229
  have hstep := st293_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p231 : ((3872574142297/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT293 (i+1))
      = (∑ i ∈ Finset.range 230, stT293 (i+1)) + stT293 231 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 230
    simpa using h
  have hprev := st293_p230
  have hstep := st293_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p232 : ((1953318578093/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT293 (i+1))
      = (∑ i ∈ Finset.range 231, stT293 (i+1)) + stT293 232 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 231
    simpa using h
  have hprev := st293_p231
  have hstep := st293_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p233 : ((651129497833/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT293 (i+1))
      = (∑ i ∈ Finset.range 232, stT293 (i+1)) + stT293 233 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 232
    simpa using h
  have hprev := st293_p232
  have hstep := st293_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p234 : ((3308634240789/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT293 (i+1))
      = (∑ i ∈ Finset.range 233, stT293 (i+1)) + stT293 234 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 233
    simpa using h
  have hprev := st293_p233
  have hstep := st293_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p235 : ((4015203751293/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT293 (i+1))
      = (∑ i ∈ Finset.range 234, stT293 (i+1)) + stT293 235 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 234
    simpa using h
  have hprev := st293_p234
  have hstep := st293_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p236 : ((15491202328197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT293 (i+1))
      = (∑ i ∈ Finset.range 235, stT293 (i+1)) + stT293 236 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 235
    simpa using h
  have hprev := st293_p235
  have hstep := st293_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p237 : ((15603304946217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT293 (i+1))
      = (∑ i ∈ Finset.range 236, stT293 (i+1)) + stT293 237 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 236
    simpa using h
  have hprev := st293_p236
  have hstep := st293_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p238 : ((16242790912273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT293 (i+1))
      = (∑ i ∈ Finset.range 237, stT293 (i+1)) + stT293 238 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 237
    simpa using h
  have hprev := st293_p237
  have hstep := st293_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p239 : ((16556154163281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT293 (i+1))
      = (∑ i ∈ Finset.range 238, stT293 (i+1)) + stT293 239 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 238
    simpa using h
  have hprev := st293_p238
  have hstep := st293_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p240 : ((16131650149557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT293 (i+1))
      = (∑ i ∈ Finset.range 239, stT293 (i+1)) + stT293 240 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 239
    simpa using h
  have hprev := st293_p239
  have hstep := st293_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p241 : ((15529873526901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT293 (i+1))
      = (∑ i ∈ Finset.range 240, stT293 (i+1)) + stT293 241 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 240
    simpa using h
  have hprev := st293_p240
  have hstep := st293_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p242 : ((621385242693/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT293 (i+1))
      = (∑ i ∈ Finset.range 241, stT293 (i+1)) + stT293 242 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 241
    simpa using h
  have hprev := st293_p241
  have hstep := st293_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p243 : ((645442236833/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT293 (i+1))
      = (∑ i ∈ Finset.range 242, stT293 (i+1)) + stT293 243 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 242
    simpa using h
  have hprev := st293_p242
  have hstep := st293_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p244 : ((16559347502177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT293 (i+1))
      = (∑ i ∈ Finset.range 243, stT293 (i+1)) + stT293 244 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 243
    simpa using h
  have hprev := st293_p243
  have hstep := st293_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p245 : ((16266646004627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT293 (i+1))
      = (∑ i ∈ Finset.range 244, stT293 (i+1)) + stT293 245 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 244
    simpa using h
  have hprev := st293_p244
  have hstep := st293_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p246 : ((7816047791323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT293 (i+1))
      = (∑ i ∈ Finset.range 245, stT293 (i+1)) + stT293 246 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 245
    simpa using h
  have hprev := st293_p245
  have hstep := st293_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p247 : ((15453955507481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT293 (i+1))
      = (∑ i ∈ Finset.range 246, stT293 (i+1)) + stT293 247 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 246
    simpa using h
  have hprev := st293_p246
  have hstep := st293_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p248 : ((15951375137481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT293 (i+1))
      = (∑ i ∈ Finset.range 247, stT293 (i+1)) + stT293 248 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 247
    simpa using h
  have hprev := st293_p247
  have hstep := st293_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p249 : ((16504871580253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT293 (i+1))
      = (∑ i ∈ Finset.range 248, stT293 (i+1)) + stT293 249 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 248
    simpa using h
  have hprev := st293_p248
  have hstep := st293_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p250 : ((16434107975781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT293 (i+1))
      = (∑ i ∈ Finset.range 249, stT293 (i+1)) + stT293 250 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 249
    simpa using h
  have hprev := st293_p249
  have hstep := st293_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p251 : ((3957261901189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT293 (i+1))
      = (∑ i ∈ Finset.range 250, stT293 (i+1)) + stT293 251 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 250
    simpa using h
  have hprev := st293_p250
  have hstep := st293_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p252 : ((15425618899713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT293 (i+1))
      = (∑ i ∈ Finset.range 251, stT293 (i+1)) + stT293 252 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 251
    simpa using h
  have hprev := st293_p251
  have hstep := st293_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p253 : ((15707745960907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT293 (i+1))
      = (∑ i ∈ Finset.range 252, stT293 (i+1)) + stT293 253 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 252
    simpa using h
  have hprev := st293_p252
  have hstep := st293_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p254 : ((8167169105141/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT293 (i+1))
      = (∑ i ∈ Finset.range 253, stT293 (i+1)) + stT293 254 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 253
    simpa using h
  have hprev := st293_p253
  have hstep := st293_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p255 : ((8280072595661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT293 (i+1))
      = (∑ i ∈ Finset.range 254, stT293 (i+1)) + stT293 255 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 254
    simpa using h
  have hprev := st293_p254
  have hstep := st293_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p256 : ((1612152448953/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT293 (i+1))
      = (∑ i ∈ Finset.range 255, stT293 (i+1)) + stT293 256 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 255
    simpa using h
  have hprev := st293_p255
  have hstep := st293_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p257 : ((3107068001971/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT293 (i+1))
      = (∑ i ∈ Finset.range 256, stT293 (i+1)) + stT293 257 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 256
    simpa using h
  have hprev := st293_p256
  have hstep := st293_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p258 : ((3096649865389/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT293 (i+1))
      = (∑ i ∈ Finset.range 257, stT293 (i+1)) + stT293 258 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 257
    simpa using h
  have hprev := st293_p257
  have hstep := st293_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p259 : ((1602211605797/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT293 (i+1))
      = (∑ i ∈ Finset.range 258, stT293 (i+1)) + stT293 259 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 258
    simpa using h
  have hprev := st293_p258
  have hstep := st293_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p260 : ((8265523693307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT293 (i+1))
      = (∑ i ∈ Finset.range 259, stT293 (i+1)) + stT293 260 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 259
    simpa using h
  have hprev := st293_p259
  have hstep := st293_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p261 : ((16431096783739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT293 (i+1))
      = (∑ i ∈ Finset.range 260, stT293 (i+1)) + stT293 261 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 260
    simpa using h
  have hprev := st293_p260
  have hstep := st293_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p262 : ((1583872070181/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT293 (i+1))
      = (∑ i ∈ Finset.range 261, stT293 (i+1)) + stT293 262 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 261
    simpa using h
  have hprev := st293_p261
  have hstep := st293_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p263 : ((1542157253631/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT293 (i+1))
      = (∑ i ∈ Finset.range 262, stT293 (i+1)) + stT293 263 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 262
    simpa using h
  have hprev := st293_p262
  have hstep := st293_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p264 : ((7821776552621/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT293 (i+1))
      = (∑ i ∈ Finset.range 263, stT293 (i+1)) + stT293 264 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 263
    simpa using h
  have hprev := st293_p263
  have hstep := st293_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p265 : ((2031884704349/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT293 (i+1))
      = (∑ i ∈ Finset.range 264, stT293 (i+1)) + stT293 265 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 264
    simpa using h
  have hprev := st293_p264
  have hstep := st293_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p266 : ((16581311115661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT293 (i+1))
      = (∑ i ∈ Finset.range 265, stT293 (i+1)) + stT293 266 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 265
    simpa using h
  have hprev := st293_p265
  have hstep := st293_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p267 : ((16267516402357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT293 (i+1))
      = (∑ i ∈ Finset.range 266, stT293 (i+1)) + stT293 267 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 266
    simpa using h
  have hprev := st293_p266
  have hstep := st293_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p268 : ((15657810688117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT293 (i+1))
      = (∑ i ∈ Finset.range 267, stT293 (i+1)) + stT293 268 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 267
    simpa using h
  have hprev := st293_p267
  have hstep := st293_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p269 : ((15410938704217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT293 (i+1))
      = (∑ i ∈ Finset.range 268, stT293 (i+1)) + stT293 269 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 268
    simpa using h
  have hprev := st293_p268
  have hstep := st293_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p270 : ((15789009900517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT293 (i+1))
      = (∑ i ∈ Finset.range 269, stT293 (i+1)) + stT293 270 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 269
    simpa using h
  have hprev := st293_p269
  have hstep := st293_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p271 : ((16386279470853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT293 (i+1))
      = (∑ i ∈ Finset.range 270, stT293 (i+1)) + stT293 271 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 270
    simpa using h
  have hprev := st293_p270
  have hstep := st293_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p272 : ((8285241113679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT293 (i+1))
      = (∑ i ∈ Finset.range 271, stT293 (i+1)) + stT293 272 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 271
    simpa using h
  have hprev := st293_p271
  have hstep := st293_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p273 : ((8075324439387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT293 (i+1))
      = (∑ i ∈ Finset.range 272, stT293 (i+1)) + stT293 273 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 272
    simpa using h
  have hprev := st293_p272
  have hstep := st293_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p274 : ((243247923873/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT293 (i+1))
      = (∑ i ∈ Finset.range 273, stT293 (i+1)) + stT293 274 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 273
    simpa using h
  have hprev := st293_p273
  have hstep := st293_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p275 : ((3856636267421/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT293 (i+1))
      = (∑ i ∈ Finset.range 274, stT293 (i+1)) + stT293 275 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 274
    simpa using h
  have hprev := st293_p274
  have hstep := st293_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p276 : ((3967369533977/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT293 (i+1))
      = (∑ i ∈ Finset.range 275, stT293 (i+1)) + stT293 276 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 275
    simpa using h
  have hprev := st293_p275
  have hstep := st293_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p277 : ((8220256908631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT293 (i+1))
      = (∑ i ∈ Finset.range 276, stT293 (i+1)) + stT293 277 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 276
    simpa using h
  have hprev := st293_p276
  have hstep := st293_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p278 : ((8279500301791/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT293 (i+1))
      = (∑ i ∈ Finset.range 277, stT293 (i+1)) + stT293 278 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 277
    simpa using h
  have hprev := st293_p277
  have hstep := st293_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p279 : ((16107945936417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT293 (i+1))
      = (∑ i ∈ Finset.range 278, stT293 (i+1)) + stT293 279 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 278
    simpa using h
  have hprev := st293_p278
  have hstep := st293_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p280 : ((7771317507621/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT293 (i+1))
      = (∑ i ∈ Finset.range 279, stT293 (i+1)) + stT293 280 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 279
    simpa using h
  have hprev := st293_p279
  have hstep := st293_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p281 : ((7713303616671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT293 (i+1))
      = (∑ i ∈ Finset.range 280, stT293 (i+1)) + stT293 281 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 280
    simpa using h
  have hprev := st293_p280
  have hstep := st293_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p282 : ((3968010114063/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT293 (i+1))
      = (∑ i ∈ Finset.range 281, stT293 (i+1)) + stT293 282 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 281
    simpa using h
  have hprev := st293_p281
  have hstep := st293_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p283 : ((4109449502907/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT293 (i+1))
      = (∑ i ∈ Finset.range 282, stT293 (i+1)) + stT293 283 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 282
    simpa using h
  have hprev := st293_p282
  have hstep := st293_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p284 : ((8285264633499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT293 (i+1))
      = (∑ i ∈ Finset.range 283, stT293 (i+1)) + stT293 284 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 283
    simpa using h
  have hprev := st293_p283
  have hstep := st293_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p285 : ((8071913555377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT293 (i+1))
      = (∑ i ∈ Finset.range 284, stT293 (i+1)) + stT293 285 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 284
    simpa using h
  have hprev := st293_p284
  have hstep := st293_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p286 : ((7786139078233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT293 (i+1))
      = (∑ i ∈ Finset.range 285, stT293 (i+1)) + stT293 286 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 285
    simpa using h
  have hprev := st293_p285
  have hstep := st293_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p287 : ((3851077025207/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT293 (i+1))
      = (∑ i ∈ Finset.range 286, stT293 (i+1)) + stT293 287 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 286
    simpa using h
  have hprev := st293_p286
  have hstep := st293_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p288 : ((15797499695423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT293 (i+1))
      = (∑ i ∈ Finset.range 287, stT293 (i+1)) + stT293 288 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 287
    simpa using h
  have hprev := st293_p287
  have hstep := st293_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p289 : ((8188321761749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT293 (i+1))
      = (∑ i ∈ Finset.range 288, stT293 (i+1)) + stT293 289 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 288
    simpa using h
  have hprev := st293_p288
  have hstep := st293_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p290 : ((8298074647799/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT293 (i+1))
      = (∑ i ∈ Finset.range 289, stT293 (i+1)) + stT293 290 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 289
    simpa using h
  have hprev := st293_p289
  have hstep := st293_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p291 : ((8126460205127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT293 (i+1))
      = (∑ i ∈ Finset.range 290, stT293 (i+1)) + stT293 291 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 290
    simpa using h
  have hprev := st293_p290
  have hstep := st293_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p292 : ((7834349948579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT293 (i+1))
      = (∑ i ∈ Finset.range 291, stT293 (i+1)) + stT293 292 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 291
    simpa using h
  have hprev := st293_p291
  have hstep := st293_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p293 : ((3845945243711/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT293 (i+1))
      = (∑ i ∈ Finset.range 292, stT293 (i+1)) + stT293 293 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 292
    simpa using h
  have hprev := st293_p292
  have hstep := st293_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p294 : ((7828825514167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT293 (i+1))
      = (∑ i ∈ Finset.range 293, stT293 (i+1)) + stT293 294 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 293
    simpa using h
  have hprev := st293_p293
  have hstep := st293_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p295 : ((405940393841/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT293 (i+1))
      = (∑ i ∈ Finset.range 294, stT293 (i+1)) + stT293 295 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 294
    simpa using h
  have hprev := st293_p294
  have hstep := st293_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p296 : ((2074595629849/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT293 (i+1))
      = (∑ i ∈ Finset.range 295, stT293 (i+1)) + stT293 296 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 295
    simpa using h
  have hprev := st293_p295
  have hstep := st293_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p297 : ((4103268982179/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT293 (i+1))
      = (∑ i ∈ Finset.range 296, stT293 (i+1)) + stT293 297 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 296
    simpa using h
  have hprev := st293_p296
  have hstep := st293_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p298 : ((15853793060481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT293 (i+1))
      = (∑ i ∈ Finset.range 297, stT293 (i+1)) + stT293 298 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 297
    simpa using h
  have hprev := st293_p297
  have hstep := st293_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p299 : ((7709028787763/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT293 (i+1))
      = (∑ i ∈ Finset.range 298, stT293 (i+1)) + stT293 299 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 298
    simpa using h
  have hprev := st293_p298
  have hstep := st293_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p300 : ((242032251409/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT293 (i+1))
      = (∑ i ∈ Finset.range 299, stT293 (i+1)) + stT293 300 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 299
    simpa using h
  have hprev := st293_p299
  have hstep := st293_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p301 : ((4000934849959/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT293 (i+1))
      = (∑ i ∈ Finset.range 300, stT293 (i+1)) + stT293 301 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 300
    simpa using h
  have hprev := st293_p300
  have hstep := st293_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p302 : ((16508337775901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT293 (i+1))
      = (∑ i ∈ Finset.range 301, stT293 (i+1)) + stT293 302 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 301
    simpa using h
  have hprev := st293_p301
  have hstep := st293_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p303 : ((16566192910573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT293 (i+1))
      = (∑ i ∈ Finset.range 302, stT293 (i+1)) + stT293 303 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 302
    simpa using h
  have hprev := st293_p302
  have hstep := st293_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p304 : ((16129830487153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT293 (i+1))
      = (∑ i ∈ Finset.range 303, stT293 (i+1)) + stT293 304 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 303
    simpa using h
  have hprev := st293_p303
  have hstep := st293_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p305 : ((1946976469013/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT293 (i+1))
      = (∑ i ∈ Finset.range 304, stT293 (i+1)) + stT293 305 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 304
    simpa using h
  have hprev := st293_p304
  have hstep := st293_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p306 : ((3844148887093/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT293 (i+1))
      = (∑ i ∈ Finset.range 305, stT293 (i+1)) + stT293 306 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 305
    simpa using h
  have hprev := st293_p305
  have hstep := st293_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p307 : ((7849420275121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT293 (i+1))
      = (∑ i ∈ Finset.range 306, stT293 (i+1)) + stT293 307 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 306
    simpa using h
  have hprev := st293_p306
  have hstep := st293_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p308 : ((8134247200861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT293 (i+1))
      = (∑ i ∈ Finset.range 307, stT293 (i+1)) + stT293 308 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 307
    simpa using h
  have hprev := st293_p307
  have hstep := st293_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p309 : ((8303834879901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT293 (i+1))
      = (∑ i ∈ Finset.range 308, stT293 (i+1)) + stT293 309 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 308
    simpa using h
  have hprev := st293_p308
  have hstep := st293_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p310 : ((4108888212859/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT293 (i+1))
      = (∑ i ∈ Finset.range 309, stT293 (i+1)) + stT293 310 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 309
    simpa using h
  have hprev := st293_p309
  have hstep := st293_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p311 : ((3974279665141/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT293 (i+1))
      = (∑ i ∈ Finset.range 310, stT293 (i+1)) + stT293 311 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 310
    simpa using h
  have hprev := st293_p310
  have hstep := st293_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p312 : ((964793778589/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT293 (i+1))
      = (∑ i ∈ Finset.range 311, stT293 (i+1)) + stT293 312 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 311
    simpa using h
  have hprev := st293_p311
  have hstep := st293_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p313 : ((1928735466923/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT293 (i+1))
      = (∑ i ∈ Finset.range 312, stT293 (i+1)) + stT293 313 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 312
    simpa using h
  have hprev := st293_p312
  have hstep := st293_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p314 : ((3969928898561/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT293 (i+1))
      = (∑ i ∈ Finset.range 313, stT293 (i+1)) + stT293 314 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 313
    simpa using h
  have hprev := st293_p313
  have hstep := st293_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p315 : ((4105150721381/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT293 (i+1))
      = (∑ i ∈ Finset.range 314, stT293 (i+1)) + stT293 315 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 314
    simpa using h
  have hprev := st293_p314
  have hstep := st293_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p316 : ((2077247090313/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT293 (i+1))
      = (∑ i ∈ Finset.range 315, stT293 (i+1)) + stT293 316 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 315
    simpa using h
  have hprev := st293_p315
  have hstep := st293_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p317 : ((2039523465073/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT293 (i+1))
      = (∑ i ∈ Finset.range 316, stT293 (i+1)) + stT293 317 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 316
    simpa using h
  have hprev := st293_p316
  have hstep := st293_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p318 : ((15757189567129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT293 (i+1))
      = (∑ i ∈ Finset.range 317, stT293 (i+1)) + stT293 318 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 317
    simpa using h
  have hprev := st293_p317
  have hstep := st293_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p319 : ((7691532572639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT293 (i+1))
      = (∑ i ∈ Finset.range 318, stT293 (i+1)) + stT293 319 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 318
    simpa using h
  have hprev := st293_p318
  have hstep := st293_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p320 : ((7743020741319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT293 (i+1))
      = (∑ i ∈ Finset.range 319, stT293 (i+1)) + stT293 320 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 319
    simpa using h
  have hprev := st293_p319
  have hstep := st293_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p321 : ((15983304584183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT293 (i+1))
      = (∑ i ∈ Finset.range 320, stT293 (i+1)) + stT293 321 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 320
    simpa using h
  have hprev := st293_p320
  have hstep := st293_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p322 : ((16487413804759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT293 (i+1))
      = (∑ i ∈ Finset.range 321, stT293 (i+1)) + stT293 322 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 321
    simpa using h
  have hprev := st293_p321
  have hstep := st293_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p323 : ((16609936167559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT293 (i+1))
      = (∑ i ∈ Finset.range 322, stT293 (i+1)) + stT293 323 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 322
    simpa using h
  have hprev := st293_p322
  have hstep := st293_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p324 : ((16258998109031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT293 (i+1))
      = (∑ i ∈ Finset.range 323, stT293 (i+1)) + stT293 324 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 323
    simpa using h
  have hprev := st293_p323
  have hstep := st293_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p325 : ((7852154933577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT293 (i+1))
      = (∑ i ∈ Finset.range 324, stT293 (i+1)) + stT293 325 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 324
    simpa using h
  have hprev := st293_p324
  have hstep := st293_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p326 : ((7683451420479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT293 (i+1))
      = (∑ i ∈ Finset.range 325, stT293 (i+1)) + stT293 326 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 325
    simpa using h
  have hprev := st293_p325
  have hstep := st293_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p327 : ((15499623633959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT293 (i+1))
      = (∑ i ∈ Finset.range 326, stT293 (i+1)) + stT293 327 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 326
    simpa using h
  have hprev := st293_p326
  have hstep := st293_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p328 : ((640024666481/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT293 (i+1))
      = (∑ i ∈ Finset.range 327, stT293 (i+1)) + stT293 328 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 327
    simpa using h
  have hprev := st293_p327
  have hstep := st293_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p329 : ((4123748272737/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT293 (i+1))
      = (∑ i ∈ Finset.range 328, stT293 (i+1)) + stT293 329 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 328
    simpa using h
  have hprev := st293_p328
  have hstep := st293_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p330 : ((16616841509817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT293 (i+1))
      = (∑ i ∈ Finset.range 329, stT293 (i+1)) + stT293 330 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 329
    simpa using h
  have hprev := st293_p329
  have hstep := st293_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p331 : ((16278385727917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT293 (i+1))
      = (∑ i ∈ Finset.range 330, stT293 (i+1)) + stT293 331 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 330
    simpa using h
  have hprev := st293_p330
  have hstep := st293_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p332 : ((15729663064699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT293 (i+1))
      = (∑ i ∈ Finset.range 331, stT293 (i+1)) + stT293 332 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 331
    simpa using h
  have hprev := st293_p331
  have hstep := st293_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p333 : ((7685517871999/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT293 (i+1))
      = (∑ i ∈ Finset.range 332, stT293 (i+1)) + stT293 333 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 332
    simpa using h
  have hprev := st293_p332
  have hstep := st293_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p334 : ((7730497845699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT293 (i+1))
      = (∑ i ∈ Finset.range 333, stT293 (i+1)) + stT293 334 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 333
    simpa using h
  have hprev := st293_p333
  have hstep := st293_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p335 : ((3983114324421/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT293 (i+1))
      = (∑ i ∈ Finset.range 334, stT293 (i+1)) + stT293 335 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 334
    simpa using h
  have hprev := st293_p334
  have hstep := st293_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p336 : ((822301730073/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT293 (i+1))
      = (∑ i ∈ Finset.range 335, stT293 (i+1)) + stT293 336 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 335
    simpa using h
  have hprev := st293_p335
  have hstep := st293_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p337 : ((2079500233527/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT293 (i+1))
      = (∑ i ∈ Finset.range 336, stT293 (i+1)) + stT293 337 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 336
    simpa using h
  have hprev := st293_p336
  have hstep := st293_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p338 : ((8184779123783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT293 (i+1))
      = (∑ i ∈ Finset.range 337, stT293 (i+1)) + stT293 338 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 337
    simpa using h
  have hprev := st293_p337
  have hstep := st293_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p339 : ((7918250901803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT293 (i+1))
      = (∑ i ∈ Finset.range 338, stT293 (i+1)) + stT293 339 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 338
    simpa using h
  have hprev := st293_p338
  have hstep := st293_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p340 : ((15411240967499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT293 (i+1))
      = (∑ i ∈ Finset.range 339, stT293 (i+1)) + stT293 340 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 339
    simpa using h
  have hprev := st293_p339
  have hstep := st293_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p341 : ((7694585435797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT293 (i+1))
      = (∑ i ∈ Finset.range 340, stT293 (i+1)) + stT293 341 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 340
    simpa using h
  have hprev := st293_p340
  have hstep := st293_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p342 : ((986467955951/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT293 (i+1))
      = (∑ i ∈ Finset.range 341, stT293 (i+1)) + stT293 342 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 341
    simpa using h
  have hprev := st293_p341
  have hstep := st293_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p343 : ((8160287822707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT293 (i+1))
      = (∑ i ∈ Finset.range 342, stT293 (i+1)) + stT293 343 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 342
    simpa using h
  have hprev := st293_p342
  have hstep := st293_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p344 : ((16631954678663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT293 (i+1))
      = (∑ i ∈ Finset.range 343, stT293 (i+1)) + stT293 344 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 343
    simpa using h
  have hprev := st293_p343
  have hstep := st293_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p345 : ((16506695799307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT293 (i+1))
      = (∑ i ∈ Finset.range 344, stT293 (i+1)) + stT293 345 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 344
    simpa using h
  have hprev := st293_p344
  have hstep := st293_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p346 : ((16031806531531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT293 (i+1))
      = (∑ i ∈ Finset.range 345, stT293 (i+1)) + stT293 346 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 345
    simpa using h
  have hprev := st293_p345
  have hstep := st293_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p347 : ((7764436188881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT293 (i+1))
      = (∑ i ∈ Finset.range 346, stT293 (i+1)) + stT293 347 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 346
    simpa using h
  have hprev := st293_p346
  have hstep := st293_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p348 : ((3066985283821/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT293 (i+1))
      = (∑ i ∈ Finset.range 347, stT293 (i+1)) + stT293 348 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 347
    simpa using h
  have hprev := st293_p347
  have hstep := st293_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p349 : ((38944043789/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT293 (i+1))
      = (∑ i ∈ Finset.range 348, stT293 (i+1)) + stT293 349 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 348
    simpa using h
  have hprev := st293_p348
  have hstep := st293_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p350 : ((2011734228727/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT293 (i+1))
      = (∑ i ∈ Finset.range 349, stT293 (i+1)) + stT293 350 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 349
    simpa using h
  have hprev := st293_p349
  have hstep := st293_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p351 : ((2067748737847/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT293 (i+1))
      = (∑ i ∈ Finset.range 350, stT293 (i+1)) + stT293 351 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 350
    simpa using h
  have hprev := st293_p350
  have hstep := st293_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p352 : ((16628470914029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT293 (i+1))
      = (∑ i ∈ Finset.range 351, stT293 (i+1)) + stT293 352 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 351
    simpa using h
  have hprev := st293_p351
  have hstep := st293_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p353 : ((16298677898901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT293 (i+1))
      = (∑ i ∈ Finset.range 352, stT293 (i+1)) + stT293 353 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 352
    simpa using h
  have hprev := st293_p352
  have hstep := st293_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p354 : ((492767998353/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT293 (i+1))
      = (∑ i ∈ Finset.range 353, stT293 (i+1)) + stT293 354 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 353
    simpa using h
  have hprev := st293_p353
  have hstep := st293_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p355 : ((1922645227377/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT293 (i+1))
      = (∑ i ∈ Finset.range 354, stT293 (i+1)) + stT293 355 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 354
    simpa using h
  have hprev := st293_p354
  have hstep := st293_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p356 : ((7692174878493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT293 (i+1))
      = (∑ i ∈ Finset.range 355, stT293 (i+1)) + stT293 356 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 355
    simpa using h
  have hprev := st293_p355
  have hstep := st293_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p357 : ((7887064667769/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT293 (i+1))
      = (∑ i ∈ Finset.range 356, stT293 (i+1)) + stT293 357 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 356
    simpa using h
  have hprev := st293_p356
  have hstep := st293_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p358 : ((8150518002159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT293 (i+1))
      = (∑ i ∈ Finset.range 357, stT293 (i+1)) + stT293 358 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 357
    simpa using h
  have hprev := st293_p357
  have hstep := st293_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p359 : ((4157876734071/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT293 (i+1))
      = (∑ i ∈ Finset.range 358, stT293 (i+1)) + stT293 359 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 358
    simpa using h
  have hprev := st293_p358
  have hstep := st293_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p360 : ((16558796059211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT293 (i+1))
      = (∑ i ∈ Finset.range 359, stT293 (i+1)) + stT293 360 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 359
    simpa using h
  have hprev := st293_p359
  have hstep := st293_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p361 : ((16130307993079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT293 (i+1))
      = (∑ i ∈ Finset.range 360, stT293 (i+1)) + stT293 361 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 360
    simpa using h
  have hprev := st293_p360
  have hstep := st293_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p362 : ((3122840544199/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT293 (i+1))
      = (∑ i ∈ Finset.range 361, stT293 (i+1)) + stT293 362 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 361
    simpa using h
  have hprev := st293_p361
  have hstep := st293_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p363 : ((15330145799331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT293 (i+1))
      = (∑ i ∈ Finset.range 362, stT293 (i+1)) + stT293 363 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 362
    simpa using h
  have hprev := st293_p362
  have hstep := st293_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p364 : ((15451778191851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT293 (i+1))
      = (∑ i ∈ Finset.range 363, stT293 (i+1)) + stT293 364 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 363
    simpa using h
  have hprev := st293_p363
  have hstep := st293_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p365 : ((79513176987/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT293 (i+1))
      = (∑ i ∈ Finset.range 364, stT293 (i+1)) + stT293 365 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 364
    simpa using h
  have hprev := st293_p364
  have hstep := st293_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p366 : ((256351460961/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT293 (i+1))
      = (∑ i ∈ Finset.range 365, stT293 (i+1)) + stT293 366 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 365
    simpa using h
  have hprev := st293_p365
  have hstep := st293_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p367 : ((16657775108569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT293 (i+1))
      = (∑ i ∈ Finset.range 366, stT293 (i+1)) + stT293 367 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 366
    simpa using h
  have hprev := st293_p366
  have hstep := st293_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p368 : ((16506198402431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT293 (i+1))
      = (∑ i ∈ Finset.range 367, stT293 (i+1)) + stT293 368 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 367
    simpa using h
  have hprev := st293_p367
  have hstep := st293_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p369 : ((16044575128591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT293 (i+1))
      = (∑ i ∈ Finset.range 368, stT293 (i+1)) + stT293 369 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 368
    simpa using h
  have hprev := st293_p368
  have hstep := st293_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p370 : ((15549781585963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT293 (i+1))
      = (∑ i ∈ Finset.range 369, stT293 (i+1)) + stT293 370 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 369
    simpa using h
  have hprev := st293_p369
  have hstep := st293_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p371 : ((15315637814363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT293 (i+1))
      = (∑ i ∈ Finset.range 370, stT293 (i+1)) + stT293 371 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 370
    simpa using h
  have hprev := st293_p370
  have hstep := st293_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p372 : ((15479139942563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT293 (i+1))
      = (∑ i ∈ Finset.range 371, stT293 (i+1)) + stT293 372 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 371
    simpa using h
  have hprev := st293_p371
  have hstep := st293_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p373 : ((15942290528103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT293 (i+1))
      = (∑ i ∈ Finset.range 372, stT293 (i+1)) + stT293 373 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 372
    simpa using h
  have hprev := st293_p372
  have hstep := st293_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p374 : ((3286577018549/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT293 (i+1))
      = (∑ i ∈ Finset.range 373, stT293 (i+1)) + stT293 374 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 373
    simpa using h
  have hprev := st293_p373
  have hstep := st293_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p375 : ((4166356085553/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT293 (i+1))
      = (∑ i ∈ Finset.range 374, stT293 (i+1)) + stT293 375 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 374
    simpa using h
  have hprev := st293_p374
  have hstep := st293_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p376 : ((8253273595799/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT293 (i+1))
      = (∑ i ∈ Finset.range 375, stT293 (i+1)) + stT293 376 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 375
    simpa using h
  have hprev := st293_p375
  have hstep := st293_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p377 : ((401238913103/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT293 (i+1))
      = (∑ i ∈ Finset.range 376, stT293 (i+1)) + stT293 377 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 376
    simpa using h
  have hprev := st293_p376
  have hstep := st293_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p378 : ((3111524615761/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT293 (i+1))
      = (∑ i ∈ Finset.range 377, stT293 (i+1)) + stT293 378 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 377
    simpa using h
  have hprev := st293_p377
  have hstep := st293_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p379 : ((15311293521173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT293 (i+1))
      = (∑ i ∈ Finset.range 378, stT293 (i+1)) + stT293 379 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 378
    simpa using h
  have hprev := st293_p378
  have hstep := st293_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p380 : ((48278355143/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT293 (i+1))
      = (∑ i ∈ Finset.range 379, stT293 (i+1)) + stT293 380 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 379
    simpa using h
  have hprev := st293_p379
  have hstep := st293_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p381 : ((3178275647887/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT293 (i+1))
      = (∑ i ∈ Finset.range 380, stT293 (i+1)) + stT293 381 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 380
    simpa using h
  have hprev := st293_p380
  have hstep := st293_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p382 : ((16388390755967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT293 (i+1))
      = (∑ i ∈ Finset.range 381, stT293 (i+1)) + stT293 382 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 381
    simpa using h
  have hprev := st293_p381
  have hstep := st293_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p383 : ((16662141549183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT293 (i+1))
      = (∑ i ∈ Finset.range 382, stT293 (i+1)) + stT293 383 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 382
    simpa using h
  have hprev := st293_p382
  have hstep := st293_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p384 : ((16561445962041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT293 (i+1))
      = (∑ i ∈ Finset.range 383, stT293 (i+1)) + stT293 384 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 383
    simpa using h
  have hprev := st293_p383
  have hstep := st293_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p385 : ((3228746469093/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT293 (i+1))
      = (∑ i ∈ Finset.range 384, stT293 (i+1)) + stT293 385 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 384
    simpa using h
  have hprev := st293_p384
  have hstep := st293_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p386 : ((3128079020233/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT293 (i+1))
      = (∑ i ∈ Finset.range 385, stT293 (i+1)) + stT293 386 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 385
    simpa using h
  have hprev := st293_p385
  have hstep := st293_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p387 : ((15327510468401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT293 (i+1))
      = (∑ i ∈ Finset.range 386, stT293 (i+1)) + stT293 387 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 386
    simpa using h
  have hprev := st293_p386
  have hstep := st293_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p388 : ((7687361267191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT293 (i+1))
      = (∑ i ∈ Finset.range 387, stT293 (i+1)) + stT293 388 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 387
    simpa using h
  have hprev := st293_p387
  have hstep := st293_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p389 : ((7877359660401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT293 (i+1))
      = (∑ i ∈ Finset.range 388, stT293 (i+1)) + stT293 389 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 388
    simpa using h
  have hprev := st293_p388
  have hstep := st293_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p390 : ((16260826528029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT293 (i+1))
      = (∑ i ∈ Finset.range 389, stT293 (i+1)) + stT293 390 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 389
    simpa using h
  have hprev := st293_p389
  have hstep := st293_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p391 : ((16620591390219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT293 (i+1))
      = (∑ i ∈ Finset.range 390, stT293 (i+1)) + stT293 391 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 390
    simpa using h
  have hprev := st293_p390
  have hstep := st293_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p392 : ((16642356630287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT293 (i+1))
      = (∑ i ∈ Finset.range 391, stT293 (i+1)) + stT293 392 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 391
    simpa using h
  have hprev := st293_p391
  have hstep := st293_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p393 : ((16316070055029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT293 (i+1))
      = (∑ i ∈ Finset.range 392, stT293 (i+1)) + stT293 393 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 392
    simpa using h
  have hprev := st293_p392
  have hstep := st293_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p394 : ((3163205256507/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT293 (i+1))
      = (∑ i ∈ Finset.range 393, stT293 (i+1)) + stT293 394 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 393
    simpa using h
  have hprev := st293_p393
  have hstep := st293_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p395 : ((1540641031281/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT293 (i+1))
      = (∑ i ∈ Finset.range 394, stT293 (i+1)) + stT293 395 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 394
    simpa using h
  have hprev := st293_p394
  have hstep := st293_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p396 : ((15301533089953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT293 (i+1))
      = (∑ i ∈ Finset.range 395, stT293 (i+1)) + stT293 396 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 395
    simpa using h
  have hprev := st293_p395
  have hstep := st293_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p397 : ((15554682880183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT293 (i+1))
      = (∑ i ∈ Finset.range 396, stT293 (i+1)) + stT293 397 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 396
    simpa using h
  have hprev := st293_p396
  have hstep := st293_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p398 : ((16032772429081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT293 (i+1))
      = (∑ i ∈ Finset.range 397, stT293 (i+1)) + stT293 398 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 397
    simpa using h
  have hprev := st293_p397
  have hstep := st293_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p399 : ((3297538655557/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT293 (i+1))
      = (∑ i ∈ Finset.range 398, stT293 (i+1)) + stT293 399 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 398
    simpa using h
  have hprev := st293_p398
  have hstep := st293_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p400 : ((3337114355557/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT293 (i+1))
      = (∑ i ∈ Finset.range 399, stT293 (i+1)) + stT293 400 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 399
    simpa using h
  have hprev := st293_p399
  have hstep := st293_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p401 : ((4131565006967/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT293 (i+1))
      = (∑ i ∈ Finset.range 400, stT293 (i+1)) + stT293 401 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 400
    simpa using h
  have hprev := st293_p400
  have hstep := st293_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p402 : ((16092506270753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT293 (i+1))
      = (∑ i ∈ Finset.range 401, stT293 (i+1)) + stT293 402 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 401
    simpa using h
  have hprev := st293_p401
  have hstep := st293_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p403 : ((15605420421641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT293 (i+1))
      = (∑ i ∈ Finset.range 402, stT293 (i+1)) + stT293 403 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 402
    simpa using h
  have hprev := st293_p402
  have hstep := st293_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p404 : ((15310992657593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT293 (i+1))
      = (∑ i ∈ Finset.range 403, stT293 (i+1)) + stT293 404 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 403
    simpa using h
  have hprev := st293_p403
  have hstep := st293_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p405 : ((3839049353553/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT293 (i+1))
      = (∑ i ∈ Finset.range 404, stT293 (i+1)) + stT293 405 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 404
    simpa using h
  have hprev := st293_p404
  have hstep := st293_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p406 : ((15716891290901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT293 (i+1))
      = (∑ i ∈ Finset.range 405, stT293 (i+1)) + stT293 406 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 405
    simpa using h
  have hprev := st293_p405
  have hstep := st293_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p407 : ((506631158137/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT293 (i+1))
      = (∑ i ∈ Finset.range 406, stT293 (i+1)) + stT293 407 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 406
    simpa using h
  have hprev := st293_p406
  have hstep := st293_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p408 : ((3319247710691/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT293 (i+1))
      = (∑ i ∈ Finset.range 407, stT293 (i+1)) + stT293 408 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 407
    simpa using h
  have hprev := st293_p407
  have hstep := st293_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p409 : ((16680215042831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT293 (i+1))
      = (∑ i ∈ Finset.range 408, stT293 (i+1)) + stT293 409 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 408
    simpa using h
  have hprev := st293_p408
  have hstep := st293_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p410 : ((8212122159733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT293 (i+1))
      = (∑ i ∈ Finset.range 409, stT293 (i+1)) + stT293 410 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 409
    simpa using h
  have hprev := st293_p409
  have hstep := st293_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p411 : ((7977393113317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT293 (i+1))
      = (∑ i ∈ Finset.range 410, stT293 (i+1)) + stT293 411 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 410
    simpa using h
  have hprev := st293_p410
  have hstep := st293_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p412 : ((7750456834367/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT293 (i+1))
      = (∑ i ∈ Finset.range 411, stT293 (i+1)) + stT293 412 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 411
    simpa using h
  have hprev := st293_p411
  have hstep := st293_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p413 : ((7641038379581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT293 (i+1))
      = (∑ i ∈ Finset.range 412, stT293 (i+1)) + stT293 413 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 412
    simpa using h
  have hprev := st293_p412
  have hstep := st293_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p414 : ((3850646730427/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT293 (i+1))
      = (∑ i ∈ Finset.range 413, stT293 (i+1)) + stT293 414 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 413
    simpa using h
  have hprev := st293_p413
  have hstep := st293_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p415 : ((3950792877307/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT293 (i+1))
      = (∑ i ∈ Finset.range 414, stT293 (i+1)) + stT293 415 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 414
    simpa using h
  have hprev := st293_p414
  have hstep := st293_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p416 : ((2036433498761/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT293 (i+1))
      = (∑ i ∈ Finset.range 415, stT293 (i+1)) + stT293 416 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 415
    simpa using h
  have hprev := st293_p415
  have hstep := st293_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p417 : ((259924902211/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT293 (i+1))
      = (∑ i ∈ Finset.range 416, stT293 (i+1)) + stT293 417 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 416
    simpa using h
  have hprev := st293_p416
  have hstep := st293_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p418 : ((8336243401897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT293 (i+1))
      = (∑ i ∈ Finset.range 417, stT293 (i+1)) + stT293 418 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 417
    simpa using h
  have hprev := st293_p417
  have hstep := st293_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p419 : ((8193556395061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT293 (i+1))
      = (∑ i ∈ Finset.range 418, stT293 (i+1)) + stT293 419 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 418
    simpa using h
  have hprev := st293_p418
  have hstep := st293_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p420 : ((7957059232087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT293 (i+1))
      = (∑ i ∈ Finset.range 419, stT293 (i+1)) + stT293 420 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 419
    simpa using h
  have hprev := st293_p419
  have hstep := st293_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p421 : ((15474825151211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT293 (i+1))
      = (∑ i ∈ Finset.range 420, stT293 (i+1)) + stT293 421 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 420
    simpa using h
  have hprev := st293_p420
  have hstep := st293_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p422 : ((15272949173353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT293 (i+1))
      = (∑ i ∈ Finset.range 421, stT293 (i+1)) + stT293 422 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 421
    simpa using h
  have hprev := st293_p421
  have hstep := st293_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p423 : ((15400696592761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT293 (i+1))
      = (∑ i ∈ Finset.range 422, stT293 (i+1)) + stT293 423 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 422
    simpa using h
  have hprev := st293_p422
  have hstep := st293_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p424 : ((15797874531683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT293 (i+1))
      = (∑ i ∈ Finset.range 423, stT293 (i+1)) + stT293 424 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 423
    simpa using h
  have hprev := st293_p423
  have hstep := st293_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p425 : ((16281450542861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT293 (i+1))
      = (∑ i ∈ Finset.range 424, stT293 (i+1)) + stT293 425 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 424
    simpa using h
  have hprev := st293_p424
  have hstep := st293_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p426 : ((332612501681/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT293 (i+1))
      = (∑ i ∈ Finset.range 425, stT293 (i+1)) + stT293 426 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 425
    simpa using h
  have hprev := st293_p425
  have hstep := st293_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p427 : ((834376054343/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT293 (i+1))
      = (∑ i ∈ Finset.range 426, stT293 (i+1)) + stT293 427 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 426
    simpa using h
  have hprev := st293_p426
  have hstep := st293_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p428 : ((4106921278543/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT293 (i+1))
      = (∑ i ∈ Finset.range 427, stT293 (i+1)) + stT293 428 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 427
    simpa using h
  have hprev := st293_p427
  have hstep := st293_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p429 : ((15969277699237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT293 (i+1))
      = (∑ i ∈ Finset.range 428, stT293 (i+1)) + stT293 429 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 428
    simpa using h
  have hprev := st293_p428
  have hstep := st293_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p430 : ((3103668961651/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT293 (i+1))
      = (∑ i ∈ Finset.range 429, stT293 (i+1)) + stT293 430 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 429
    simpa using h
  have hprev := st293_p429
  have hstep := st293_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p431 : ((3055157120959/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT293 (i+1))
      = (∑ i ∈ Finset.range 430, stT293 (i+1)) + stT293 431 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 430
    simpa using h
  have hprev := st293_p430
  have hstep := st293_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p432 : ((3069662654809/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT293 (i+1))
      = (∑ i ∈ Finset.range 431, stT293 (i+1)) + stT293 432 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 431
    simpa using h
  have hprev := st293_p431
  have hstep := st293_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p433 : ((3925633609137/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT293 (i+1))
      = (∑ i ∈ Finset.range 432, stT293 (i+1)) + stT293 433 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 432
    simpa using h
  have hprev := st293_p432
  have hstep := st293_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p434 : ((8090727981189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT293 (i+1))
      = (∑ i ∈ Finset.range 433, stT293 (i+1)) + stT293 434 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 433
    simpa using h
  have hprev := st293_p433
  have hstep := st293_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p435 : ((4143714078201/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT293 (i+1))
      = (∑ i ∈ Finset.range 434, stT293 (i+1)) + stT293 435 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 434
    simpa using h
  have hprev := st293_p434
  have hstep := st293_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p436 : ((334232121773/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT293 (i+1))
      = (∑ i ∈ Finset.range 435, stT293 (i+1)) + stT293 436 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 435
    simpa using h
  have hprev := st293_p435
  have hstep := st293_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p437 : ((3306686182439/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT293 (i+1))
      = (∑ i ∈ Finset.range 436, stT293 (i+1)) + stT293 437 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 436
    simpa using h
  have hprev := st293_p436
  have hstep := st293_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p438 : ((16118603746603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT293 (i+1))
      = (∑ i ∈ Finset.range 437, stT293 (i+1)) + stT293 438 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 437
    simpa using h
  have hprev := st293_p437
  have hstep := st293_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p439 : ((15646548260519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT293 (i+1))
      = (∑ i ∈ Finset.range 438, stT293 (i+1)) + stT293 439 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 438
    simpa using h
  have hprev := st293_p438
  have hstep := st293_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p440 : ((15319646930603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT293 (i+1))
      = (∑ i ∈ Finset.range 439, stT293 (i+1)) + stT293 440 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 439
    simpa using h
  have hprev := st293_p439
  have hstep := st293_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p441 : ((15276654502359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT293 (i+1))
      = (∑ i ∈ Finset.range 440, stT293 (i+1)) + stT293 441 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 440
    simpa using h
  have hprev := st293_p440
  have hstep := st293_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p442 : ((15534619065699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT293 (i+1))
      = (∑ i ∈ Finset.range 441, stT293 (i+1)) + stT293 442 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 441
    simpa using h
  have hprev := st293_p441
  have hstep := st293_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p443 : ((639329039221/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT293 (i+1))
      = (∑ i ∈ Finset.range 442, stT293 (i+1)) + stT293 443 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 442
    simpa using h
  have hprev := st293_p442
  have hstep := st293_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p444 : ((16432859686267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT293 (i+1))
      = (∑ i ∈ Finset.range 443, stT293 (i+1)) + stT293 444 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 443
    simpa using h
  have hprev := st293_p443
  have hstep := st293_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p445 : ((16695087158917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT293 (i+1))
      = (∑ i ∈ Finset.range 444, stT293 (i+1)) + stT293 445 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 444
    simpa using h
  have hprev := st293_p444
  have hstep := st293_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p446 : ((16661254110103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT293 (i+1))
      = (∑ i ∈ Finset.range 445, stT293 (i+1)) + stT293 446 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 445
    simpa using h
  have hprev := st293_p445
  have hstep := st293_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p447 : ((16346629883143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT293 (i+1))
      = (∑ i ∈ Finset.range 446, stT293 (i+1)) + stT293 447 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 446
    simpa using h
  have hprev := st293_p446
  have hstep := st293_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p448 : ((15882488163831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT293 (i+1))
      = (∑ i ∈ Finset.range 447, stT293 (i+1)) + stT293 448 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 447
    simpa using h
  have hprev := st293_p447
  have hstep := st293_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p449 : ((15460589822781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT293 (i+1))
      = (∑ i ∈ Finset.range 448, stT293 (i+1)) + stT293 449 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 448
    simpa using h
  have hprev := st293_p448
  have hstep := st293_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p450 : ((15253758993411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT293 (i+1))
      = (∑ i ∈ Finset.range 449, stT293 (i+1)) + stT293 450 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 449
    simpa using h
  have hprev := st293_p449
  have hstep := st293_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p451 : ((15345553477313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT293 (i+1))
      = (∑ i ∈ Finset.range 450, stT293 (i+1)) + stT293 451 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 450
    simpa using h
  have hprev := st293_p450
  have hstep := st293_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p452 : ((15697395927393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT293 (i+1))
      = (∑ i ∈ Finset.range 451, stT293 (i+1)) + stT293 452 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 451
    simpa using h
  have hprev := st293_p451
  have hstep := st293_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p453 : ((16165759220273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT293 (i+1))
      = (∑ i ∈ Finset.range 452, stT293 (i+1)) + stT293 453 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 452
    simpa using h
  have hprev := st293_p452
  have hstep := st293_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p454 : ((1656133233473/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT293 (i+1))
      = (∑ i ∈ Finset.range 453, stT293 (i+1)) + stT293 454 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 453
    simpa using h
  have hprev := st293_p453
  have hstep := st293_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p455 : ((418139706083/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT293 (i+1))
      = (∑ i ∈ Finset.range 454, stT293 (i+1)) + stT293 455 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 454
    simpa using h
  have hprev := st293_p454
  have hstep := st293_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p456 : ((16593797012623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT293 (i+1))
      = (∑ i ∈ Finset.range 455, stT293 (i+1)) + stT293 456 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 455
    simpa using h
  have hprev := st293_p455
  have hstep := st293_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p457 : ((16219609635103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT293 (i+1))
      = (∑ i ∈ Finset.range 456, stT293 (i+1)) + stT293 457 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 456
    simpa using h
  have hprev := st293_p456
  have hstep := st293_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p458 : ((15752295711723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT293 (i+1))
      = (∑ i ∈ Finset.range 457, stT293 (i+1)) + stT293 458 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 457
    simpa using h
  have hprev := st293_p457
  have hstep := st293_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p459 : ((15376666996407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT293 (i+1))
      = (∑ i ∈ Finset.range 458, stT293 (i+1)) + stT293 459 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 458
    simpa using h
  have hprev := st293_p458
  have hstep := st293_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p460 : ((7619980575277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT293 (i+1))
      = (∑ i ∈ Finset.range 459, stT293 (i+1)) + stT293 460 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 459
    simpa using h
  have hprev := st293_p459
  have hstep := st293_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p461 : ((3848678061311/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT293 (i+1))
      = (∑ i ∈ Finset.range 460, stT293 (i+1)) + stT293 461 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 460
    simpa using h
  have hprev := st293_p460
  have hstep := st293_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p462 : ((1972425396981/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT293 (i+1))
      = (∑ i ∈ Finset.range 461, stT293 (i+1)) + stT293 462 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 461
    simpa using h
  have hprev := st293_p461
  have hstep := st293_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p463 : ((16243787579991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT293 (i+1))
      = (∑ i ∈ Finset.range 462, stT293 (i+1)) + stT293 463 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 462
    simpa using h
  have hprev := st293_p462
  have hstep := st293_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p464 : ((16608036142599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT293 (i+1))
      = (∑ i ∈ Finset.range 463, stT293 (i+1)) + stT293 464 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 463
    simpa using h
  have hprev := st293_p463
  have hstep := st293_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p465 : ((3346465162029/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT293 (i+1))
      = (∑ i ∈ Finset.range 464, stT293 (i+1)) + stT293 465 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 464
    simpa using h
  have hprev := st293_p464
  have hstep := st293_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p466 : ((16569965511291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT293 (i+1))
      = (∑ i ∈ Finset.range 465, stT293 (i+1)) + stT293 466 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 465
    simpa using h
  have hprev := st293_p465
  have hstep := st293_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p467 : ((8092028039663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT293 (i+1))
      = (∑ i ∈ Finset.range 466, stT293 (i+1)) + stT293 467 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 466
    simpa using h
  have hprev := st293_p466
  have hstep := st293_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p468 : ((15722166097357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT293 (i+1))
      = (∑ i ∈ Finset.range 467, stT293 (i+1)) + stT293 468 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 467
    simpa using h
  have hprev := st293_p467
  have hstep := st293_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p469 : ((15359439026827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT293 (i+1))
      = (∑ i ∈ Finset.range 468, stT293 (i+1)) + stT293 469 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 468
    simpa using h
  have hprev := st293_p468
  have hstep := st293_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p470 : ((15232213099973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT293 (i+1))
      = (∑ i ∈ Finset.range 469, stT293 (i+1)) + stT293 470 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 469
    simpa using h
  have hprev := st293_p469
  have hstep := st293_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p471 : ((7693653830549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT293 (i+1))
      = (∑ i ∈ Finset.range 470, stT293 (i+1)) + stT293 471 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 470
    simpa using h
  have hprev := st293_p470
  have hstep := st293_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p472 : ((3153118998467/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT293 (i+1))
      = (∑ i ∈ Finset.range 471, stT293 (i+1)) + stT293 472 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 471
    simpa using h
  have hprev := st293_p471
  have hstep := st293_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p473 : ((3245060606467/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT293 (i+1))
      = (∑ i ∈ Finset.range 472, stT293 (i+1)) + stT293 473 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 472
    simpa using h
  have hprev := st293_p472
  have hstep := st293_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p474 : ((3319119087259/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT293 (i+1))
      = (∑ i ∈ Finset.range 473, stT293 (i+1)) + stT293 474 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 473
    simpa using h
  have hprev := st293_p473
  have hstep := st293_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p475 : ((837001657047/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT293 (i+1))
      = (∑ i ∈ Finset.range 474, stT293 (i+1)) + stT293 475 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 474
    simpa using h
  have hprev := st293_p474
  have hstep := st293_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p476 : ((1660636132199/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT293 (i+1))
      = (∑ i ∈ Finset.range 475, stT293 (i+1)) + stT293 476 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 475
    simpa using h
  have hprev := st293_p475
  have hstep := st293_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p477 : ((16244623292147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT293 (i+1))
      = (∑ i ∈ Finset.range 476, stT293 (i+1)) + stT293 477 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 476
    simpa using h
  have hprev := st293_p476
  have hstep := st293_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p478 : ((15787680619567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT293 (i+1))
      = (∑ i ∈ Finset.range 477, stT293 (i+1)) + stT293 478 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 477
    simpa using h
  have hprev := st293_p477
  have hstep := st293_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p479 : ((15401945000191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT293 (i+1))
      = (∑ i ∈ Finset.range 478, stT293 (i+1)) + stT293 479 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 478
    simpa using h
  have hprev := st293_p478
  have hstep := st293_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p480 : ((15226744780207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT293 (i+1))
      = (∑ i ∈ Finset.range 479, stT293 (i+1)) + stT293 480 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 479
    simpa using h
  have hprev := st293_p479
  have hstep := st293_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p481 : ((15324384510567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT293 (i+1))
      = (∑ i ∈ Finset.range 480, stT293 (i+1)) + stT293 481 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 480
    simpa using h
  have hprev := st293_p480
  have hstep := st293_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p482 : ((15658744763631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT293 (i+1))
      = (∑ i ∈ Finset.range 481, stT293 (i+1)) + stT293 482 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 481
    simpa using h
  have hprev := st293_p481
  have hstep := st293_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p483 : ((16109318817231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT293 (i+1))
      = (∑ i ∈ Finset.range 482, stT293 (i+1)) + stT293 483 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 482
    simpa using h
  have hprev := st293_p482
  have hstep := st293_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p484 : ((16515166593201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT293 (i+1))
      = (∑ i ∈ Finset.range 483, stT293 (i+1)) + stT293 484 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 483
    simpa using h
  have hprev := st293_p483
  have hstep := st293_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p485 : ((16732485550497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT293 (i+1))
      = (∑ i ∈ Finset.range 484, stT293 (i+1)) + stT293 485 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 484
    simpa using h
  have hprev := st293_p484
  have hstep := st293_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p486 : ((16685190811067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT293 (i+1))
      = (∑ i ∈ Finset.range 485, stT293 (i+1)) + stT293 486 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 485
    simpa using h
  have hprev := st293_p485
  have hstep := st293_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p487 : ((16390936316939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT293 (i+1))
      = (∑ i ∈ Finset.range 486, stT293 (i+1)) + stT293 487 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 486
    simpa using h
  have hprev := st293_p486
  have hstep := st293_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p488 : ((7976897761807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT293 (i+1))
      = (∑ i ∈ Finset.range 487, stT293 (i+1)) + stT293 488 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 487
    simpa using h
  have hprev := st293_p487
  have hstep := st293_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p489 : ((7763457010291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT293 (i+1))
      = (∑ i ∈ Finset.range 488, stT293 (i+1)) + stT293 489 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 488
    simpa using h
  have hprev := st293_p488
  have hstep := st293_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p490 : ((7629338927509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT293 (i+1))
      = (∑ i ∈ Finset.range 489, stT293 (i+1)) + stT293 490 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 489
    simpa using h
  have hprev := st293_p489
  have hstep := st293_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p491 : ((3810345051823/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT293 (i+1))
      = (∑ i ∈ Finset.range 490, stT293 (i+1)) + stT293 491 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 490
    simpa using h
  have hprev := st293_p490
  have hstep := st293_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p492 : ((7740004448831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT293 (i+1))
      = (∑ i ∈ Finset.range 491, stT293 (i+1)) + stT293 492 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 491
    simpa using h
  have hprev := st293_p491
  have hstep := st293_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p493 : ((15891566552901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT293 (i+1))
      = (∑ i ∈ Finset.range 492, stT293 (i+1)) + stT293 493 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 492
    simpa using h
  have hprev := st293_p492
  have hstep := st293_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p494 : ((8167256213819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT293 (i+1))
      = (∑ i ∈ Finset.range 493, stT293 (i+1)) + stT293 494 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 493
    simpa using h
  have hprev := st293_p493
  have hstep := st293_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p495 : ((8328845533343/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT293 (i+1))
      = (∑ i ∈ Finset.range 494, stT293 (i+1)) + stT293 495 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 494
    simpa using h
  have hprev := st293_p494
  have hstep := st293_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p496 : ((16751780393797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT293 (i+1))
      = (∑ i ∈ Finset.range 495, stT293 (i+1)) + stT293 496 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 495
    simpa using h
  have hprev := st293_p495
  have hstep := st293_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p497 : ((16585805725367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT293 (i+1))
      = (∑ i ∈ Finset.range 496, stT293 (i+1)) + stT293 497 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 496
    simpa using h
  have hprev := st293_p496
  have hstep := st293_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p498 : ((1621666667123/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT293 (i+1))
      = (∑ i ∈ Finset.range 497, stT293 (i+1)) + stT293 498 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 497
    simpa using h
  have hprev := st293_p497
  have hstep := st293_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p499 : ((197112642327/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT293 (i+1))
      = (∑ i ∈ Finset.range 498, stT293 (i+1)) + stT293 499 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 498
    simpa using h
  have hprev := st293_p498
  have hstep := st293_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_p500 : ((7696396975151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT293 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT293 (i+1))
      = (∑ i ∈ Finset.range 499, stT293 (i+1)) + stT293 500 := by
    have h := Finset.sum_range_succ (fun i => stT293 (i+1)) 499
    simpa using h
  have hprev := st293_p499
  have hstep := st293_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st293_s500 :
    |Real.sin (((293 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))
      - ((-270403/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -3212747/5000000) (δ := 14819/1000000000) (ψ := 1326617/1000000) 293 290
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 293`** (evaluated boundary). -/
theorem station_293_sign : 0 < hardyG ((((293:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 293 500 (by norm_num) (by norm_num)
    ((1326617/1000000 : ℚ) : ℝ)
  have hchain := st293_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT293 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((293 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((1326617/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st293_c500
  have hsinb := abs_le.mp st293_s500
  have hbdy_lo : ((142077228045519/3433970000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((293 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ))) / 2
          - ((((293:ℕ)):ℝ))
            * Real.sin (((293 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((1326617/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((293:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((293:ℝ) * Real.log (500:ℝ) - ((1326617/1000000 : ℚ) : ℝ))) / 2
        - ((293:ℝ)) * Real.sin ((293:ℝ) * Real.log (500:ℝ) - ((1326617/1000000 : ℚ) : ℝ))
        ≥ ((317694763/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((293:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((317694763/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((317694763/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((317694763/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((293:ℕ)):ℝ))+1) * (((((293:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((670747880511/1000000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((7696396975151/5000000000000 : ℚ) : ℝ) + ((142077228045519/3433970000000000 : ℚ) : ℝ)
      - ((670747880511/1000000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((1326617/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((293:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((1326617/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((293:ℕ)):ℝ)))).re
      - Real.sin ((1326617/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((293:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((293:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((293:ℕ)):ℝ))
      = (((((293:ℕ)):ℝ)) * (Real.log ((((293:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((293:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_293
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
  have hθwin : |(((1326617/1000000 : ℚ) : ℝ) + ((66:ℤ)) * (2*Real.pi)) - theta ((((293:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((293:ℕ)):ℝ)))
    (φ := ((1326617/1000000 : ℚ) : ℝ) + ((66:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((1326617/1000000 : ℚ)) : ℝ) 66).1,
    (cos_sin_shift (((1326617/1000000 : ℚ)) : ℝ) 66).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_293_sign
end AxiomAudit
