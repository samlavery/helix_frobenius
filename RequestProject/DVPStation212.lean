import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 212` (rung-217.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT212 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((212 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))

theorem st212_c1 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((908277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 539561/5000000) (δ := 201/1000000000) (ψ := -431649/1000000) 212 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t1 : ((908227/1000000 : ℚ) : ℝ) ≤ stT212 1 := by
  have hc : ((908227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((908227/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((908227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c2 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-19243/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7163957/10000000) (δ := 10667/1000000000) (ψ := -431649/1000000) 212 23
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t2 : ((-8504727037/12500000000 : ℚ) : ℝ) ≤ stT212 2 := by
  have hc : ((-4811/5000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8504727037/12500000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-4811/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c3 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((163187/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1074487/5000000) (δ := 2659/250000000) (ψ := -431649/1000000) 212 37
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t3 : ((942088302099/2500000000000 : ℚ) : ℝ) ≤ stT212 3 := by
  have hc : ((326349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((942088302099/2500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((326349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c4 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((553981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1229573/5000000) (δ := 2691/250000000) (ψ := -431649/1000000) 212 47
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t4 : ((553931/2000000 : ℚ) : ℝ) ≤ stT212 4 := by
  have hc : ((553931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((553931/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((553931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c5 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-347957/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 292561/500000) (δ := 10789/1000000000) (ψ := -431649/1000000) 212 54
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t5 : ((-97263926847/312500000000 : ℚ) : ℝ) ≤ stT212 5 := by
  have hc : ((-173991/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97263926847/312500000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-173991/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c6 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-988479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -467133/625000) (δ := 10739/1000000000) (ψ := -431649/1000000) 212 61
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t6 : ((-4035652837507/10000000000000 : ℚ) : ℝ) ≤ stT212 6 := by
  have hc : ((-988529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4035652837507/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-988529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c7 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-30843/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2157037/5000000) (δ := 1341/125000000) (ψ := -431649/1000000) 212 66
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t7 : ((-23322677437/400000000000 : ℚ) : ℝ) ≤ stT212 7 := by
  have hc : ((-30853/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23322677437/400000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-30853/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c8 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((120219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 725143/2000000) (δ := 10699/1000000000) (ψ := -431649/1000000) 212 70
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t8 : ((424861465077/10000000000000 : ℚ) : ℝ) ≤ stT212 8 := by
  have hc : ((120169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((424861465077/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((120169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c9 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((279483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 804713/2500000) (δ := 1067/100000000) (ψ := -431649/1000000) 212 74
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t9 : ((931443240189/10000000000000 : ℚ) : ℝ) ≤ stT212 9 := by
  have hc : ((279433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((931443240189/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((279433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c10 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((30991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -117873/312500) (δ := 10641/1000000000) (ψ := -431649/1000000) 212 78
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t10 : ((48961534791/2500000000000 : ℚ) : ℝ) ≤ stT212 10 := by
  have hc : ((15483/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48961534791/2500000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((15483/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c11 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((30887/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19071/500000) (δ := 67/6250000) (ψ := -431649/1000000) 212 81
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t11 : ((1489969345871/5000000000000 : ℚ) : ℝ) ≤ stT212 11 := by
  have hc : ((494167/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1489969345871/5000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((494167/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c12 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((106191/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -347317/2500000) (δ := 5399/500000000) (ψ := -431649/1000000) 212 84
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t12 : ((1226115732989/5000000000000 : ℚ) : ℝ) ≤ stT212 12 := by
  have hc : ((424739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1226115732989/5000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((424739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c13 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-190341/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3045263/5000000) (δ := 5363/500000000) (ψ := -431649/1000000) 212 87
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t13 : ((-1055891245207/5000000000000 : ℚ) : ℝ) ≤ stT212 13 := by
  have hc : ((-380707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1055891245207/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-380707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c14 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((759459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1770787/10000000) (δ := 10663/1000000000) (ψ := -431649/1000000) 212 89
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t14 : ((507401401577/2500000000000 : ℚ) : ℝ) ≤ stT212 14 := by
  have hc : ((759409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((507401401577/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((759409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c15 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-465591/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3460549/5000000) (δ := 2151/200000000) (ψ := -431649/1000000) 212 91
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t15 : ((-75138461889/312500000000 : ℚ) : ℝ) ≤ stT212 15 := by
  have hc : ((-29101/31250 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75138461889/312500000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-29101/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c16 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-736687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5997387/10000000) (δ := 2669/250000000) (ψ := -431649/1000000) 212 94
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t16 : ((-1841843236737/10000000000000 : ℚ) : ℝ) ≤ stT212 16 := by
  have hc : ((-736737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1841843236737/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-736737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c17 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-128987/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1320569/2500000) (δ := 1339/125000000) (ψ := -431649/1000000) 212 96
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t17 : ((-625739680643/5000000000000 : ℚ) : ℝ) ≤ stT212 17 := by
  have hc : ((-257999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-625739680643/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-257999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c18 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-836521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25617/40000) (δ := 2141/200000000) (ψ := -431649/1000000) 212 98
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t18 : ((-1971817088133/10000000000000 : ℚ) : ℝ) ≤ stT212 18 := by
  have hc : ((-836571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1971817088133/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-836571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c19 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-865709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3271701/5000000) (δ := 10791/1000000000) (ψ := -431649/1000000) 212 99
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t19 : ((-993093967961/5000000000000 : ℚ) : ℝ) ≤ stT212 19 := by
  have hc : ((-865759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-993093967961/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-865759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c20 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((601699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 92517/400000) (δ := 10627/1000000000) (ψ := -431649/1000000) 212 101
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t20 : ((1345327474483/10000000000000 : ℚ) : ℝ) ≤ stT212 20 := by
  have hc : ((601649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1345327474483/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((601649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c21 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((53947/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -811049/2500000) (δ := 5381/500000000) (ψ := -431649/1000000) 212 103
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t21 : ((58850067393/1000000000000 : ℚ) : ℝ) ≤ stT212 21 := by
  have hc : ((53937/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58850067393/1000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((53937/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c22 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-326137/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5703441/10000000) (δ := 2131/200000000) (ψ := -431649/1000000) 212 104
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t22 : ((-43461249581/312500000000 : ℚ) : ℝ) ≤ stT212 22 := by
  have hc : ((-163081/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43461249581/312500000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-163081/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c23 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((325759/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2153031/10000000) (δ := 10763/1000000000) (ψ := -431649/1000000) 212 106
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t23 : ((42450143481/312500000000 : ℚ) : ℝ) ≤ stT212 23 := by
  have hc : ((162867/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42450143481/312500000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((162867/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c24 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-15131/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4695593/10000000) (δ := 10733/1000000000) (ψ := -431649/1000000) 212 107
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t24 : ((-30891135807/500000000000 : ℚ) : ℝ) ≤ stT212 24 := by
  have hc : ((-30267/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30891135807/500000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-30267/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c25 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-446699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5084673/10000000) (δ := 2671/250000000) (ψ := -431649/1000000) 212 109
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t25 : ((-893498446749/10000000000000 : ℚ) : ℝ) ≤ stT212 25 := by
  have hc : ((-446749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-893498446749/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-446749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c26 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((999997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1133/2000000) (δ := 10791/1000000000) (ψ := -431649/1000000) 212 110
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t26 : ((1961057058467/10000000000000 : ℚ) : ℝ) ≤ stT212 26 := by
  have hc : ((999947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1961057058467/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((999947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c27 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-144191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 428873/1000000) (δ := 2141/200000000) (ψ := -431649/1000000) 212 111
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t27 : ((-277591948741/10000000000000 : ℚ) : ℝ) ≤ stT212 27 := by
  have hc : ((-144241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277591948741/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-144241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c28 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1570463/2000000) (δ := 10713/1000000000) (ψ := -431649/1000000) 212 113
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t28 : ((-37798349823/200000000000 : ℚ) : ℝ) ≤ stT212 28 := by
  have hc : ((-20001/20000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37798349823/200000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-20001/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c29 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-201119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -496189/1000000) (δ := 10783/1000000000) (ψ := -431649/1000000) 212 114
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t29 : ((-23344697211/312500000000 : ℚ) : ℝ) ≤ stT212 29 := by
  have hc : ((-25143/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23344697211/312500000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-25143/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c30 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((235301/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1351029/5000000) (δ := 2669/250000000) (ψ := -431649/1000000) 212 115
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t30 : ((107388259879/1250000000000 : ℚ) : ℝ) ≤ stT212 30 := by
  have hc : ((58819/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107388259879/1250000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((58819/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c31 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((458051/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -515687/5000000) (δ := 5317/500000000) (ψ := -431649/1000000) 212 116
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t31 : ((411319485689/2500000000000 : ℚ) : ℝ) ≤ stT212 31 := by
  have hc : ((229013/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((411319485689/2500000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((229013/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c32 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((249847/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 43737/5000000) (δ := 5371/500000000) (ψ := -431649/1000000) 212 117
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t32 : ((441648934727/2500000000000 : ℚ) : ℝ) ≤ stT212 32 := by
  have hc : ((499669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((441648934727/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((499669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c33 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((962321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 344229/5000000) (δ := 5377/500000000) (ψ := -431649/1000000) 212 118
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t33 : ((209387282787/1250000000000 : ℚ) : ℝ) ≤ stT212 33 := by
  have hc : ((962271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209387282787/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((962271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c34 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((94891/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 160517/2000000) (δ := 10647/1000000000) (ψ := -431649/1000000) 212 119
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t34 : ((16272806671/100000000000 : ℚ) : ℝ) ≤ stT212 34 := by
  have hc : ((47443/50000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16272806671/100000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((47443/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c35 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((491633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 457997/10000000) (δ := 10663/1000000000) (ψ := -431649/1000000) 212 120
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t35 : ((25967779227/156250000000 : ℚ) : ℝ) ≤ stT212 35 := by
  have hc : ((61451/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25967779227/156250000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((61451/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c36 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((19837/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -319389/10000000) (δ := 1077/100000000) (ψ := -431649/1000000) 212 121
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t36 : ((4132498347/25000000000 : ℚ) : ℝ) ≤ stT212 36 := by
  have hc : ((4959/5000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4132498347/25000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((4959/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c37 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((164801/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1505883/10000000) (δ := 5363/500000000) (ψ := -431649/1000000) 212 122
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t37 : ((270914591299/2000000000000 : ℚ) : ℝ) ≤ stT212 37 := by
  have hc : ((164791/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270914591299/2000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((164791/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c38 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((66493/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -30797/100000) (δ := 5309/500000000) (ψ := -431649/1000000) 212 123
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t38 : ((53924826681/1000000000000 : ℚ) : ℝ) ≤ stT212 38 := by
  have hc : ((66483/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53924826681/1000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((66483/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c39 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-423643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -627581/1250000) (δ := 2673/250000000) (ψ := -431649/1000000) 212 124
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t39 : ((-339225987213/5000000000000 : ℚ) : ℝ) ≤ stT212 39 := by
  have hc : ((-423693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-339225987213/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-423693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c40 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-195287/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7310177/10000000) (δ := 10799/1000000000) (ψ := -431649/1000000) 212 125
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t40 : ((-308791703283/2000000000000 : ℚ) : ℝ) ≤ stT212 40 := by
  have hc : ((-195297/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-308791703283/2000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-195297/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c41 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-674261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5776901/10000000) (δ := 10799/1000000000) (ψ := -431649/1000000) 212 125
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t41 : ((-526548556259/5000000000000 : ℚ) : ℝ) ≤ stT212 41 := by
  have hc : ((-674311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-526548556259/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-674311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c42 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((52623/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 568133/2000000) (δ := 10697/1000000000) (ψ := -431649/1000000) 212 126
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t42 : ((324757526411/5000000000000 : ℚ) : ℝ) ≤ stT212 42 := by
  have hc : ((210467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((324757526411/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((210467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c43 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((987473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -396133/10000000) (δ := 10613/1000000000) (ψ := -431649/1000000) 212 127
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t43 : ((301161052731/2000000000000 : ℚ) : ℝ) ≤ stT212 43 := by
  have hc : ((987423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((301161052731/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((987423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c44 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((733/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3919661/10000000) (δ := 67/6250000) (ψ := -431649/1000000) 212 128
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t44 : ((543097049/1250000000000 : ℚ) : ℝ) ≤ stT212 44 := by
  have hc : ((1441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((543097049/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((1441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c45 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-1997/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7717041/10000000) (δ := 431/40000000) (ψ := -431649/1000000) 212 129
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t45 : ((-3721376169/25000000000 : ℚ) : ℝ) ≤ stT212 45 := by
  have hc : ((-19971/20000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3721376169/25000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-19971/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c46 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-957/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30717/78125) (δ := 431/40000000) (ψ := -431649/1000000) 212 129
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t46 : ((-36197011/125000000000 : ℚ) : ℝ) ≤ stT212 46 := by
  have hc : ((-491/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36197011/125000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-491/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c47 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((4943/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47231/1250000) (δ := 2667/250000000) (ψ := -431649/1000000) 212 130
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t47 : ((28838949379/200000000000 : ℚ) : ℝ) ≤ stT212 47 := by
  have hc : ((19771/20000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28838949379/200000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((19771/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c48 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-389609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4927509/10000000) (δ := 5321/500000000) (ψ := -431649/1000000) 212 131
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t48 : ((-35151528049/625000000000 : ℚ) : ℝ) ≤ stT212 48 := by
  have hc : ((-389659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35151528049/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-389659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c49 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-368787/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6000667/10000000) (δ := 5321/500000000) (ψ := -431649/1000000) 212 131
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t49 : ((-32929656029/312500000000 : ℚ) : ℝ) ≤ stT212 49 := by
  have hc : ((-92203/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32929656029/312500000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-92203/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c50 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((115129/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 250047/2500000) (δ := 10749/1000000000) (ψ := -431649/1000000) 212 132
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t50 : ((651232358583/5000000000000 : ℚ) : ℝ) ≤ stT212 50 := by
  have hc : ((460491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((651232358583/5000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((460491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c51 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-22783/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2106199/5000000) (δ := 10747/1000000000) (ψ := -431649/1000000) 212 133
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t51 : ((-31916604833/2000000000000 : ℚ) : ℝ) ≤ stT212 51 := by
  have hc : ((-22793/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31916604833/2000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-22793/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c52 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-379209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1215839/2000000) (δ := 10747/1000000000) (ψ := -431649/1000000) 212 133
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t52 : ((-262951564367/2500000000000 : ℚ) : ℝ) ≤ stT212 52 := by
  have hc : ((-189617/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-262951564367/2500000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-189617/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c53 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((49131/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 233389/5000000) (δ := 10639/1000000000) (ψ := -431649/1000000) 212 134
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t53 : ((26993261297/200000000000 : ℚ) : ℝ) ≤ stT212 53 := by
  have hc : ((98257/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26993261297/200000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((98257/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c54 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-106737/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1333593/2500000) (δ := 10671/1000000000) (ψ := -431649/1000000) 212 135
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t54 : ((-36316076629/500000000000 : ℚ) : ℝ) ≤ stT212 54 := by
  have hc : ((-106747/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36316076629/500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-106747/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c55 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-184403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4390651/10000000) (δ := 10671/1000000000) (ψ := -431649/1000000) 212 135
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t55 : ((-621791063/25000000000 : ℚ) : ℝ) ≤ stT212 55 := by
  have hc : ((-184453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-621791063/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-184453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c56 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((95039/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1767507/10000000) (δ := 5389/500000000) (ψ := -431649/1000000) 212 136
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t56 : ((253985668043/2500000000000 : ℚ) : ℝ) ≤ stT212 56 := by
  have hc : ((380131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((253985668043/2500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((380131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c57 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-995369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7613281/10000000) (δ := 5389/500000000) (ψ := -431649/1000000) 212 136
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t57 : ((-1318465314327/10000000000000 : ℚ) : ℝ) ≤ stT212 57 := by
  have hc : ((-995419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1318465314327/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-995419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c58 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((563/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1122971/10000000) (δ := 5359/500000000) (ψ := -431649/1000000) 212 137
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t58 : ((591371199/5000000000 : ℚ) : ℝ) ≤ stT212 58 := by
  have hc : ((3603/4000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((591371199/5000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((3603/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c59 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-9321/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -34531/62500) (δ := 10611/1000000000) (ψ := -431649/1000000) 212 138
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t59 : ((-38834988133/500000000000 : ℚ) : ℝ) ≤ stT212 59 := by
  have hc : ((-298297/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38834988133/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-298297/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c60 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((5399/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3382803/10000000) (δ := 10611/1000000000) (ψ := -431649/1000000) 212 138
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t60 : ((13936925727/500000000000 : ℚ) : ℝ) ≤ stT212 60 := by
  have hc : ((21591/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13936925727/500000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((21591/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c61 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((144437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3564631/10000000) (δ := 10699/1000000000) (ψ := -431649/1000000) 212 139
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t61 : ((11554280901/625000000000 : ℚ) : ℝ) ≤ stT212 61 := by
  have hc : ((144387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11554280901/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((144387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c62 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-87097/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2526717/5000000) (δ := 10699/1000000000) (ψ := -431649/1000000) 212 139
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t62 : ((-55313032107/1000000000000 : ℚ) : ℝ) ≤ stT212 62 := by
  have hc : ((-87107/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55313032107/1000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-87107/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c63 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((129007/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1087159/5000000) (δ := 2699/250000000) (ψ := -431649/1000000) 212 140
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t63 : ((162520869357/2000000000000 : ℚ) : ℝ) ≤ stT212 63 := by
  have hc : ((128997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162520869357/2000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((128997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c64 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-391077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6172281/10000000) (δ := 2699/250000000) (ψ := -431649/1000000) 212 140
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t64 : ((-244438945551/2500000000000 : ℚ) : ℝ) ≤ stT212 64 := by
  have hc : ((-195551/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244438945551/2500000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-195551/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c65 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((864127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -164807/1250000) (δ := 10689/1000000000) (ψ := -431649/1000000) 212 141
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t65 : ((1071755314719/10000000000000 : ℚ) : ℝ) ≤ stT212 65 := by
  have hc : ((864077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1071755314719/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((864077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c66 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-908019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6773319/10000000) (δ := 10689/1000000000) (ψ := -431649/1000000) 212 141
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t66 : ((-223551150627/2000000000000 : ℚ) : ℝ) ≤ stT212 66 := by
  have hc : ((-908069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223551150627/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-908069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c67 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((926489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -964557/10000000) (δ := 10621/1000000000) (ψ := -431649/1000000) 212 142
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t67 : ((565912483833/5000000000000 : ℚ) : ℝ) ≤ stT212 67 := by
  have hc : ((926439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((565912483833/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((926439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c68 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-926191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3443723/5000000) (δ := 10621/1000000000) (ψ := -431649/1000000) 212 142
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t68 : ((-1123233009639/10000000000000 : ℚ) : ℝ) ≤ stT212 68 := by
  have hc : ((-926241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1123233009639/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-926241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c69 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((907601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1083153/10000000) (δ := 1341/125000000) (ψ := -431649/1000000) 212 143
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t69 : ((546281265879/5000000000000 : ℚ) : ℝ) ≤ stT212 69 := by
  have hc : ((907551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((546281265879/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((907551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c70 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-541/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3271429/5000000) (δ := 1341/125000000) (ψ := -431649/1000000) 212 143
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t70 : ((-20692999677/200000000000 : ℚ) : ℝ) ≤ stT212 70 := by
  have hc : ((-17313/20000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20692999677/200000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-17313/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c71 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((395331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -411817/2500000) (δ := 673/62500000) (ψ := -431649/1000000) 212 144
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t71 : ((234570824993/2500000000000 : ℚ) : ℝ) ≤ stT212 71 := by
  have hc : ((197653/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234570824993/2500000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((197653/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c72 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-335439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5765471/10000000) (δ := 673/62500000) (ψ := -431649/1000000) 212 144
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t72 : ((-3088658981/39062500000 : ℚ) : ℝ) ≤ stT212 72 := by
  have hc : ((-41933/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3088658981/39062500000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-41933/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c73 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((3961/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2632043/10000000) (δ := 533/50000000) (ψ := -431649/1000000) 212 145
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t73 : ((23177649033/400000000000 : ℚ) : ℝ) ≤ stT212 73 := by
  have hc : ((19803/40000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23177649033/400000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((19803/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c74 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-64457/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183157/400000) (δ := 533/50000000) (ψ := -431649/1000000) 212 145
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t74 : ((-149888621903/5000000000000 : ℚ) : ℝ) ≤ stT212 74 := by
  have hc : ((-128939/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149888621903/5000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-128939/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c75 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-17557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -802959/2000000) (δ := 213/20000000) (ψ := -431649/1000000) 212 146
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t75 : ((-10150976491/2500000000000 : ℚ) : ℝ) ≤ stT212 75 := by
  have hc : ((-8791/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10150976491/2500000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-8791/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c76 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((360433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3005161/10000000) (δ := 213/20000000) (ψ := -431649/1000000) 212 146
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t76 : ((206693705437/5000000000000 : ℚ) : ℝ) ≤ stT212 76 := by
  have hc : ((360383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((206693705437/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((360383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c77 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-336789/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5774589/10000000) (δ := 10757/1000000000) (ψ := -431649/1000000) 212 147
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t77 : ((-95958813821/1250000000000 : ℚ) : ℝ) ≤ stT212 77 := by
  have hc : ((-168407/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95958813821/1250000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-168407/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c78 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((227689/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1064213/10000000) (δ := 10757/1000000000) (ψ := -431649/1000000) 212 147
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t78 : ((515585728781/5000000000000 : ℚ) : ℝ) ≤ stT212 78 := by
  have hc : ((455353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((515585728781/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((455353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c79 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-249971/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7815883/10000000) (δ := 10757/1000000000) (ψ := -431649/1000000) 212 147
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t79 : ((-17578339753/156250000000 : ℚ) : ℝ) ≤ stT212 79 := by
  have hc : ((-499967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17578339753/156250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-499967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c80 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((882273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1225317/10000000) (δ := 10739/1000000000) (ψ := -431649/1000000) 212 148
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t80 : ((986354427359/10000000000000 : ℚ) : ℝ) ≤ stT212 80 := by
  have hc : ((882223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((986354427359/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((882223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c81 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-541859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 334913/625000) (δ := 10739/1000000000) (ψ := -431649/1000000) 212 148
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t81 : ((-75265199101/1250000000000 : ℚ) : ℝ) ≤ stT212 81 := by
  have hc : ((-541909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75265199101/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-541909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c82 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((3231/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1923101/5000000) (δ := 1329/125000000) (ψ := -431649/1000000) 212 149
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t82 : ((356252019/100000000000 : ℚ) : ℝ) ≤ stT212 82 := by
  have hc : ((1613/50000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((356252019/100000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((1613/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c83 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((256871/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 128907/500000) (δ := 1329/125000000) (ψ := -431649/1000000) 212 149
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t83 : ((70481239283/1250000000000 : ℚ) : ℝ) ≤ stT212 83 := by
  have hc : ((128423/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70481239283/1250000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((128423/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c84 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-454773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -52988/78125) (δ := 853/40000000) (ψ := -431649/1000000) 212 150
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t84 : ((-24811277491/250000000000 : ℚ) : ℝ) ≤ stT212 84 := by
  have hc : ((-227399/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24811277491/250000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-227399/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c85 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((979247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -102041/2000000) (δ := 5339/500000000) (ψ := -431649/1000000) 212 150
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t85 : ((265521996111/2500000000000 : ℚ) : ℝ) ≤ stT212 85 := by
  have hc : ((979197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265521996111/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((979197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c86 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-129557/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 227547/400000) (δ := 5339/500000000) (ψ := -431649/1000000) 212 150
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t86 : ((-17464465497/250000000000 : ℚ) : ℝ) ≤ stT212 86 := by
  have hc : ((-129567/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17464465497/250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-129567/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c87 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((13991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3892011/10000000) (δ := 5393/500000000) (ψ := -431649/1000000) 212 151
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t87 : ((934144587/625000000000 : ℚ) : ℝ) ≤ stT212 87 := by
  have hc : ((13941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((934144587/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((13941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c88 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((323909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5413/25000) (δ := 5393/500000000) (ψ := -431649/1000000) 212 151
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t88 : ((86315328913/1250000000000 : ℚ) : ℝ) ≤ stT212 88 := by
  have hc : ((80971/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86315328913/1250000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((80971/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c89 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-992811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7554029/10000000) (δ := 1071/100000000) (ψ := -431649/1000000) 212 152
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t89 : ((-526215337139/5000000000000 : ℚ) : ℝ) ≤ stT212 89 := by
  have hc : ((-992861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-526215337139/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-992861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c90 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((397171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -81609/500000) (δ := 1071/100000000) (ψ := -431649/1000000) 212 152
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t90 : ((52328552679/625000000000 : ℚ) : ℝ) ≤ stT212 90 := by
  have hc : ((198573/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52328552679/625000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((198573/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c91 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-5931/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4224241/10000000) (δ := 21293/1000000000) (ψ := -431649/1000000) 212 152
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t91 : ((-2487999619/200000000000 : ℚ) : ℝ) ≤ stT212 91 := by
  have hc : ((-11867/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2487999619/200000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-11867/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c92 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-648593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2845663/5000000) (δ := 10603/1000000000) (ψ := -431649/1000000) 212 153
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t92 : ((-676257678439/10000000000000 : ℚ) : ℝ) ≤ stT212 92 := by
  have hc : ((-648643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-676257678439/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-648643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c93 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((499941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38451/10000000) (δ := 10603/1000000000) (ψ := -431649/1000000) 212 153
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t93 : ((129597099029/1250000000000 : ℚ) : ℝ) ≤ stT212 93 := by
  have hc : ((124979/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129597099029/1250000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((124979/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c94 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-32667/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71337/125000) (δ := 10603/1000000000) (ψ := -431649/1000000) 212 153
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t94 : ((-33696041029/500000000000 : ℚ) : ℝ) ≤ stT212 94 := by
  have hc : ((-65339/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33696041029/500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-65339/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c95 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-92563/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -439249/1000000) (δ := 10707/1000000000) (ψ := -431649/1000000) 212 154
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t95 : ((-23748335913/1250000000000 : ℚ) : ℝ) ≤ stT212 95 := by
  have hc : ((-23147/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23748335913/1250000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-23147/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c96 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((894753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1157299/10000000) (δ := 10707/1000000000) (ψ := -431649/1000000) 212 154
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t96 : ((45657588793/500000000000 : ℚ) : ℝ) ≤ stT212 96 := by
  have hc : ((894703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45657588793/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((894703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c97 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-886181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6649583/10000000) (δ := 10707/1000000000) (ψ := -431649/1000000) 212 154
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t97 : ((-899831987157/10000000000000 : ℚ) : ℝ) ≤ stT212 97 := by
  have hc : ((-886231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-899831987157/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-886231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c98 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((121521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -905609/2500000) (δ := 10789/1000000000) (ψ := -431649/1000000) 212 155
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t98 : ((15338021699/1250000000000 : ℚ) : ℝ) ≤ stT212 98 := by
  have hc : ((121471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15338021699/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((121471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c99 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((76269/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13737/78125) (δ := 10789/1000000000) (ψ := -431649/1000000) 212 155
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t99 : ((9581017721/125000000000 : ℚ) : ℝ) ≤ stT212 99 := by
  have hc : ((9533/12500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9581017721/125000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((9533/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c100 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-190613/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1416999/2000000) (δ := 10789/1000000000) (ψ := -431649/1000000) 212 155
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t100 : ((-190623/2000000 : ℚ) : ℝ) ≤ stT212 100 := by
  have hc : ((-190623/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190623/2000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-190623/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c101 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((229043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -418657/1250000) (δ := 10681/1000000000) (ψ := -431649/1000000) 212 156
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t101 : ((227856507741/10000000000000 : ℚ) : ℝ) ≤ stT212 101 := by
  have hc : ((228993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227856507741/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((228993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c102 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((36619/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1872463/10000000) (δ := 10681/1000000000) (ψ := -431649/1000000) 212 156
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t102 : ((72511435251/1000000000000 : ℚ) : ℝ) ≤ stT212 102 := by
  have hc : ((73233/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72511435251/1000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((73233/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c103 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-947869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1760799/2500000) (δ := 10681/1000000000) (ψ := -431649/1000000) 212 156
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t103 : ((-93401302827/1000000000000 : ℚ) : ℝ) ≤ stT212 103 := by
  have hc : ((-947919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93401302827/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-947919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c104 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((76307/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -88599/250000) (δ := 10629/1000000000) (ψ := -431649/1000000) 212 157
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t104 : ((1870015089/125000000000 : ℚ) : ℝ) ≤ stT212 104 := by
  have hc : ((38141/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1870015089/125000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((38141/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c105 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((818989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12223/80000) (δ := 10629/1000000000) (ψ := -431649/1000000) 212 157
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t105 : ((7992025701/100000000000 : ℚ) : ℝ) ≤ stT212 105 := by
  have hc : ((818939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7992025701/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((818939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c106 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-867343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3275793/5000000) (δ := 10629/1000000000) (ψ := -431649/1000000) 212 157
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t106 : ((-421243338699/5000000000000 : ℚ) : ℝ) ≤ stT212 106 := by
  have hc : ((-867393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-421243338699/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-867393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c107 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-20189/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4179783/10000000) (δ := 671/62500000) (ψ := -431649/1000000) 212 158
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t107 : ((-19527120663/2000000000000 : ℚ) : ℝ) ≤ stT212 107 := by
  have hc : ((-20199/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19527120663/2000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-20199/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c108 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((955279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 750489/10000000) (δ := 671/62500000) (ψ := -431649/1000000) 212 158
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t108 : ((3676676421/40000000000 : ℚ) : ℝ) ≤ stT212 108 := by
  have hc : ((955229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3676676421/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((955229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c109 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-63137/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5635287/10000000) (δ := 671/62500000) (ψ := -431649/1000000) 212 158
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t109 : ((-30239556217/500000000000 : ℚ) : ℝ) ≤ stT212 109 := by
  have hc : ((-31571/50000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30239556217/500000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-31571/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c110 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-19951/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1308113/2500000) (δ := 269/25000000) (ψ := -431649/1000000) 212 159
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t110 : ((-19024447239/400000000000 : ℚ) : ℝ) ≤ stT212 110 := by
  have hc : ((-19953/40000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19024447239/400000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-19953/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c111 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((98483/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87201/2000000) (δ := 269/25000000) (ψ := -431649/1000000) 212 159
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t111 : ((46735541523/500000000000 : ℚ) : ℝ) ≤ stT212 111 := by
  have hc : ((49239/50000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46735541523/500000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((49239/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c112 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-155511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4317353/10000000) (δ := 269/25000000) (ψ := -431649/1000000) 212 159
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t112 : ((-9186965977/625000000000 : ℚ) : ℝ) ≤ stT212 112 := by
  have hc : ((-155561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9186965977/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-155561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c113 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-891651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83493/125000) (δ := 10653/1000000000) (ψ := -431649/1000000) 212 160
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t113 : ((-838841856421/10000000000000 : ℚ) : ℝ) ≤ stT212 113 := by
  have hc : ((-891701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-838841856421/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-891701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c114 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((693883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1004911/5000000) (δ := 10653/1000000000) (ψ := -431649/1000000) 212 160
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t114 : ((129966716061/2000000000000 : ℚ) : ℝ) ≤ stT212 114 := by
  have hc : ((693833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((129966716061/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((693833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c115 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((249819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2619039/10000000) (δ := 10653/1000000000) (ψ := -431649/1000000) 212 160
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t115 : ((14558369011/312500000000 : ℚ) : ℝ) ≤ stT212 115 := by
  have hc : ((124897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14558369011/312500000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((124897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c116 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-966779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7207779/10000000) (δ := 10653/1000000000) (ψ := -431649/1000000) 212 160
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t116 : ((-897678489433/10000000000000 : ℚ) : ℝ) ≤ stT212 116 := by
  have hc : ((-966829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-897678489433/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-966829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c117 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-1189/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -395077/1000000) (δ := 10657/1000000000) (ψ := -431649/1000000) 212 161
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t117 : ((-4420039281/5000000000000 : ℚ) : ℝ) ≤ stT212 117 := by
  have hc : ((-4781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4420039281/5000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-4781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c118 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((487513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 559901/10000000) (δ := 10657/1000000000) (ψ := -431649/1000000) 212 161
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t118 : ((3506006079/39062500000 : ℚ) : ℝ) ≤ stT212 118 := by
  have hc : ((15234/15625 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3506006079/39062500000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((15234/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c119 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-5349/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1006493/2000000) (δ := 10657/1000000000) (ψ := -431649/1000000) 212 161
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t119 : ((-39231967103/1000000000000 : ℚ) : ℝ) ≤ stT212 119 := by
  have hc : ((-42797/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39231967103/1000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-42797/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c120 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-159763/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6240299/10000000) (δ := 2153/200000000) (ψ := -431649/1000000) 212 162
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t120 : ((-145852138283/2000000000000 : ℚ) : ℝ) ≤ stT212 120 := by
  have hc : ((-159773/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145852138283/2000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-159773/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c121 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((4629/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -368387/2000000) (δ := 2153/200000000) (ψ := -431649/1000000) 212 162
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t121 : ((6732629631/100000000000 : ℚ) : ℝ) ≤ stT212 121 := by
  have hc : ((74059/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6732629631/100000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((74059/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c122 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((133369/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 252023/1000000) (δ := 2153/200000000) (ψ := -431649/1000000) 212 162
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t122 : ((241470481541/5000000000000 : ℚ) : ℝ) ≤ stT212 122 := by
  have hc : ((266713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((241470481541/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((266713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c123 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-183987/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6846779/10000000) (δ := 2153/200000000) (ψ := -431649/1000000) 212 162
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t123 : ((-16590457499/200000000000 : ℚ) : ℝ) ≤ stT212 123 := by
  have hc : ((-183997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16590457499/200000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-183997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c124 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-254249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4569669/10000000) (δ := 10731/1000000000) (ψ := -431649/1000000) 212 163
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t124 : ((-228367368073/10000000000000 : ℚ) : ℝ) ≤ stT212 124 := by
  have hc : ((-254299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228367368073/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-254299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c125 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((992193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -312603/10000000) (δ := 10731/1000000000) (ψ := -431649/1000000) 212 163
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t125 : ((887399487061/10000000000000 : ℚ) : ℝ) ≤ stT212 125 := by
  have hc : ((992143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((887399487061/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((992143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c126 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((6579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3910543/10000000) (δ := 10731/1000000000) (ψ := -431649/1000000) 212 163
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t126 : ((581649023/1000000000000 : ℚ) : ℝ) ≤ stT212 126 := by
  have hc : ((6529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((581649023/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((6529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c127 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-62197/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7607717/10000000) (δ := 83/7812500) (ψ := -431649/1000000) 212 164
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t127 : ((-441549730557/5000000000000 : ℚ) : ℝ) ≤ stT212 127 := by
  have hc : ((-497601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-441549730557/5000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-497601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c128 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((94659/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3450821/10000000) (δ := 83/7812500) (ψ := -431649/1000000) 212 164
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t128 : ((41822691911/2500000000000 : ℚ) : ℝ) ≤ stT212 128 := by
  have hc : ((47317/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41822691911/2500000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((47317/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c129 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((192781/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 134749/2000000) (δ := 83/7812500) (ψ := -431649/1000000) 212 164
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t129 : ((3394504539/40000000000 : ℚ) : ℝ) ≤ stT212 129 := by
  have hc : ((192771/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3394504539/40000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((192771/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c130 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-82373/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 953281/2000000) (δ := 83/7812500) (ψ := -431649/1000000) 212 164
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t130 : ((-144513888489/5000000000000 : ℚ) : ℝ) ≤ stT212 130 := by
  have hc : ((-164771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144513888489/5000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-164771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c131 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-925097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6880221/10000000) (δ := 5343/500000000) (ψ := -431649/1000000) 212 165
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t131 : ((-161661111927/2000000000000 : ℚ) : ℝ) ≤ stT212 131 := by
  have hc : ((-925147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161661111927/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-925147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c132 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((417673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2849783/10000000) (δ := 5343/500000000) (ψ := -431649/1000000) 212 165
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t132 : ((90873511931/2500000000000 : ℚ) : ℝ) ≤ stT212 132 := by
  have hc : ((417623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90873511931/2500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((417623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c133 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((896011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1150233/10000000) (δ := 5343/500000000) (ψ := -431649/1000000) 212 165
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t133 : ((776895846749/10000000000000 : ℚ) : ℝ) ≤ stT212 133 := by
  have hc : ((895961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((776895846749/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((895961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c134 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-91879/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5120277/10000000) (δ := 21317/1000000000) (ψ := -431649/1000000) 212 165
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t134 : ((-79380058541/2000000000000 : ℚ) : ℝ) ≤ stT212 134 := by
  have hc : ((-91889/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79380058541/2000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-91889/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c135 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-221433/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3323581/5000000) (δ := 10793/1000000000) (ψ := -431649/1000000) 212 166
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t135 : ((-381179896733/5000000000000 : ℚ) : ℝ) ≤ stT212 135 := by
  have hc : ((-442891/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-381179896733/5000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-442891/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c136 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((458683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2735709/10000000) (δ := 10793/1000000000) (ψ := -431649/1000000) 212 166
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t136 : ((98318532109/2500000000000 : ℚ) : ℝ) ≤ stT212 136 := by
  have hc : ((458633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98318532109/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((458633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c137 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((896563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 286781/2500000) (δ := 10793/1000000000) (ψ := -431649/1000000) 212 166
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t137 : ((765942157141/10000000000000 : ℚ) : ℝ) ≤ stT212 137 := by
  have hc : ((896513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((765942157141/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((896513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c138 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-416749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1000331/2000000) (δ := 10793/1000000000) (ψ := -431649/1000000) 212 166
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t138 : ((-354803066343/10000000000000 : ℚ) : ℝ) ≤ stT212 138 := by
  have hc : ((-416799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-354803066343/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-416799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c139 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-184999/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137591/200000) (δ := 10703/1000000000) (ψ := -431649/1000000) 212 167
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t139 : ((-156922598701/2000000000000 : ℚ) : ℝ) ≤ stT212 139 := by
  have hc : ((-185009/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156922598701/2000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-185009/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c140 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((16613/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -616049/2000000) (δ := 10703/1000000000) (ψ := -431649/1000000) 212 167
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t140 : ((14038430517/500000000000 : ℚ) : ℝ) ≤ stT212 140 := by
  have hc : ((33221/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14038430517/500000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((33221/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c141 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((961937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 691977/10000000) (δ := 10703/1000000000) (ψ := -431649/1000000) 212 167
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t141 : ((810054098937/10000000000000 : ℚ) : ℝ) ≤ stT212 141 := by
  have hc : ((961887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((810054098937/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((961887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c142 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-25353/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4437593/10000000) (δ := 10703/1000000000) (ψ := -431649/1000000) 212 167
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t142 : ((-42562052267/2500000000000 : ℚ) : ℝ) ≤ stT212 142 := by
  have hc : ((-101437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42562052267/2500000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-101437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c143 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-992667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3775521/5000000) (δ := 663/62500000) (ψ := -431649/1000000) 212 168
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t143 : ((-830152642231/10000000000000 : ℚ) : ℝ) ≤ stT212 143 := by
  have hc : ((-992717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-830152642231/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-992717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c144 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((27719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -964421/2500000) (δ := 663/62500000) (ψ := -431649/1000000) 212 168
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t144 : ((23057490777/10000000000000 : ℚ) : ℝ) ≤ stT212 144 := by
  have hc : ((27669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23057490777/10000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((27669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c145 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((997119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -189819/10000000) (δ := 663/62500000) (ψ := -431649/1000000) 212 168
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t145 : ((414009969663/5000000000000 : ℚ) : ℝ) ≤ stT212 145 := by
  have hc : ((997069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((414009969663/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((997069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c146 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((94267/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1726409/5000000) (δ := 663/62500000) (ψ := -431649/1000000) 212 168
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t146 : ((7799515041/500000000000 : ℚ) : ℝ) ≤ stT212 146 := by
  have hc : ((47121/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7799515041/500000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((47121/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c147 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-951299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1414109/2000000) (δ := 663/62500000) (ψ := -431649/1000000) 212 168
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t147 : ((-784660287663/10000000000000 : ℚ) : ℝ) ≤ stT212 147 := by
  have hc : ((-951349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-784660287663/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-951349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c148 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-432149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5044177/10000000) (δ := 2143/200000000) (ψ := -431649/1000000) 212 169
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t148 : ((-71053083401/2000000000000 : ℚ) : ℝ) ≤ stT212 148 := by
  have hc : ((-432199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71053083401/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-432199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c149 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((415459/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46097/312500) (δ := 2143/200000000) (ψ := -431649/1000000) 212 169
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t149 : ((170168205627/2500000000000 : ℚ) : ℝ) ≤ stT212 149 := by
  have hc : ((207717/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170168205627/2500000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((207717/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c150 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((338173/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2070013/10000000) (δ := 2143/200000000) (ψ := -431649/1000000) 212 169
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t150 : ((4314007647/78125000000 : ℚ) : ℝ) ≤ stT212 150 := by
  have hc : ((84537/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4314007647/78125000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((84537/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c151 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-617739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5591651/10000000) (δ := 2143/200000000) (ψ := -431649/1000000) 212 169
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t151 : ((-502749892521/10000000000000 : ℚ) : ℝ) ≤ stT212 151 := by
  have hc : ((-617789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-502749892521/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-617789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c152 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-440123/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3308971/5000000) (δ := 10781/1000000000) (ψ := -431649/1000000) 212 170
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t152 : ((-22312972749/312500000000 : ℚ) : ℝ) ≤ stT212 152 := by
  have hc : ((-110037/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22312972749/312500000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-110037/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c153 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((38583/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -78563/250000) (δ := 10781/1000000000) (ψ := -431649/1000000) 212 170
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t153 : ((31187450691/1250000000000 : ℚ) : ℝ) ≤ stT212 153 := by
  have hc : ((154307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31187450691/1250000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((154307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c154 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((248077/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 310271/10000000) (δ := 10781/1000000000) (ψ := -431649/1000000) 212 170
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t154 : ((199895831519/2500000000000 : ℚ) : ℝ) ≤ stT212 154 := by
  have hc : ((496129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199895831519/2500000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((496129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c155 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((74449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 467587/1250000) (δ := 10781/1000000000) (ψ := -431649/1000000) 212 170
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t155 : ((59758690381/10000000000000 : ℚ) : ℝ) ≤ stT212 155 := by
  have hc : ((74399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59758690381/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((74399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c156 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-960511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7149073/10000000) (δ := 10781/1000000000) (ψ := -431649/1000000) 212 170
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t156 : ((-769064519601/10000000000000 : ℚ) : ℝ) ≤ stT212 156 := by
  have hc : ((-960561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-769064519601/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-960561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c157 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-477777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -646537/1250000) (δ := 5337/500000000) (ψ := -431649/1000000) 212 171
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t157 : ((-381347516949/10000000000000 : ℚ) : ℝ) ≤ stT212 157 := by
  have hc : ((-477827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-381347516949/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-477827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c158 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((374949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -90361/500000) (δ := 5337/500000000) (ψ := -431649/1000000) 212 171
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t158 : ((74568353167/1250000000000 : ℚ) : ℝ) ≤ stT212 158 := by
  have hc : ((93731/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74568353167/1250000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((93731/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c159 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((102121/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96041/625000) (δ := 5337/500000000) (ψ := -431649/1000000) 212 171
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t159 : ((323928818409/5000000000000 : ℚ) : ℝ) ≤ stT212 159 := by
  have hc : ((408459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((323928818409/5000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((408459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c160 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-364431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 607443/1250000) (δ := 5337/500000000) (ψ := -431649/1000000) 212 171
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t160 : ((-28814774417/1000000000000 : ℚ) : ℝ) ≤ stT212 160 := by
  have hc : ((-364481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28814774417/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-364481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c161 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-496217/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3773127/5000000) (δ := 2659/250000000) (ψ := -431649/1000000) 212 172
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t161 : ((-195546889431/2500000000000 : ℚ) : ℝ) ≤ stT212 161 := by
  have hc : ((-248121/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195546889431/2500000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-248121/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c162 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-2103/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2132247/5000000) (δ := 2659/250000000) (ψ := -431649/1000000) 212 172
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t162 : ((-2115697067/200000000000 : ℚ) : ℝ) ≤ stT212 162 := by
  have hc : ((-67321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2115697067/200000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-67321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c163 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((230151/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1002927/10000000) (δ := 2659/250000000) (ψ := -431649/1000000) 212 172
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t163 : ((18025828151/250000000000 : ℚ) : ℝ) ≤ stT212 163 := by
  have hc : ((460277/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18025828151/250000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((460277/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c164 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((625157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2238659/10000000) (δ := 2659/250000000) (ψ := -431649/1000000) 212 172
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t164 : ((122031513219/2500000000000 : ℚ) : ℝ) ≤ stT212 164 := by
  have hc : ((625107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122031513219/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((625107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c165 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-575663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5460529/10000000) (δ := 2659/250000000) (ψ := -431649/1000000) 212 172
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t165 : ((-448191994787/10000000000000 : ℚ) : ℝ) ≤ stT212 165 := by
  have hc : ((-575713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-448191994787/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-575713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c166 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-948101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1409003/2000000) (δ := 1343/125000000) (ψ := -431649/1000000) 212 173
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t166 : ((-735908346801/10000000000000 : ℚ) : ℝ) ≤ stT212 166 := by
  have hc : ((-948151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-735908346801/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-948151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c167 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((26081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1930891/5000000) (δ := 1343/125000000) (ψ := -431649/1000000) 212 173
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t167 : ((20143386513/10000000000000 : ℚ) : ℝ) ≤ stT212 167 := by
  have hc : ((26031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20143386513/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((26031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c168 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((961317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -697629/10000000) (δ := 1343/125000000) (ψ := -431649/1000000) 212 173
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t168 : ((185408217693/2500000000000 : ℚ) : ℝ) ≤ stT212 168 := by
  have hc : ((961267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185408217693/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((961267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c169 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((139437/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 489563/2000000) (δ := 1343/125000000) (ψ := -431649/1000000) 212 173
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t169 : ((21449901627/500000000000 : ℚ) : ℝ) ≤ stT212 169 := by
  have hc : ((278849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21449901627/500000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((278849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c170 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-612379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 43552/78125) (δ := 1343/125000000) (ψ := -431649/1000000) 212 173
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t170 : ((-93942321597/2000000000000 : ℚ) : ℝ) ≤ stT212 170 := by
  have hc : ((-612429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93942321597/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-612429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c171 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-1891/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1404961/2000000) (δ := 21/1953125) (ψ := -431649/1000000) 212 174
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t171 : ((-180770249/2500000000 : ℚ) : ℝ) ≤ stT212 171 := by
  have hc : ((-18911/20000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180770249/2500000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-18911/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c172 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-119/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -983607/2500000) (δ := 21/1953125) (ψ := -431649/1000000) 212 174
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t172 : ((-92261653/400000000000 : ℚ) : ℝ) ≤ stT212 172 := by
  have hc : ((-121/40000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92261653/400000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-121/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c173 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((235287/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -172393/2000000) (δ := 21/1953125) (ψ := -431649/1000000) 212 174
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t173 : ((71550269293/1000000000000 : ℚ) : ℝ) ≤ stT212 173 := by
  have hc : ((470549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71550269293/1000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((470549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c174 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((639369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 548199/2500000) (δ := 21/1953125) (ψ := -431649/1000000) 212 174
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t174 : ((242333227631/5000000000000 : ℚ) : ℝ) ≤ stT212 174 := by
  have hc : ((639319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242333227631/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((639319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c175 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-124487/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5230067/10000000) (δ := 21/1953125) (ψ := -431649/1000000) 212 174
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t175 : ((-188225565071/5000000000000 : ℚ) : ℝ) ≤ stT212 175 := by
  have hc : ((-248999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188225565071/5000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-248999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c176 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-987479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1864489/2500000) (δ := 2129/200000000) (ψ := -431649/1000000) 212 175
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t176 : ((-744378622091/10000000000000 : ℚ) : ℝ) ≤ stT212 176 := by
  have hc : ((-987529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-744378622091/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-987529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c177 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-209669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2227541/5000000) (δ := 2129/200000000) (ψ := -431649/1000000) 212 175
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t177 : ((-157634657193/10000000000000 : ℚ) : ℝ) ≤ stT212 177 := by
  have hc : ((-209719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157634657193/10000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-209719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c178 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((208059/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -91823/625000) (δ := 2129/200000000) (ψ := -431649/1000000) 212 175
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t178 : ((311874602383/5000000000000 : ℚ) : ℝ) ≤ stT212 178 := by
  have hc : ((416093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311874602383/5000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((416093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c179 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((206331/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1500051/10000000) (δ := 2129/200000000) (ψ := -431649/1000000) 212 175
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t179 : ((61683867219/1000000000000 : ℚ) : ℝ) ≤ stT212 179 := by
  have hc : ((412637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61683867219/1000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((412637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c180 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-20873/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4452681/10000000) (δ := 2129/200000000) (ψ := -431649/1000000) 212 175
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t180 : ((-1945192821/125000000000 : ℚ) : ℝ) ≤ stT212 180 := by
  have hc : ((-10439/50000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1945192821/125000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-10439/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c181 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-30711/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7388987/10000000) (δ := 2129/200000000) (ψ := -431649/1000000) 212 175
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t181 : ((-73051181259/1000000000000 : ℚ) : ℝ) ≤ stT212 181 := by
  have hc : ((-491401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73051181259/1000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-491401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c182 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-555329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -674861/1250000) (δ := 2133/200000000) (ψ := -431649/1000000) 212 176
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t182 : ((-329339747/8000000000 : ℚ) : ℝ) ≤ stT212 182 := by
  have hc : ((-555379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-329339747/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-555379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c183 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((542067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2494753/10000000) (δ := 2133/200000000) (ψ := -431649/1000000) 212 176
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t183 : ((400670348757/10000000000000 : ℚ) : ℝ) ≤ stT212 183 := by
  have hc : ((542017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((400670348757/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((542017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c184 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((246909/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 78707/2000000) (δ := 2133/200000000) (ψ := -431649/1000000) 212 176
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t184 : ((364028643737/5000000000000 : ℚ) : ℝ) ≤ stT212 184 := by
  have hc : ((493793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((364028643737/5000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((493793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c185 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((130627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 816547/2500000) (δ := 2133/200000000) (ψ := -431649/1000000) 212 176
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t185 : ((24005104707/1250000000000 : ℚ) : ℝ) ≤ stT212 185 := by
  have hc : ((65301/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24005104707/1250000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((65301/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c186 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-3849/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 382707/625000) (δ := 2133/200000000) (ψ := -431649/1000000) 212 176
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t186 : ((-2822408673/50000000000 : ℚ) : ℝ) ≤ stT212 186 := by
  have hc : ((-15397/20000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2822408673/50000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-15397/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c187 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-225709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6742791/10000000) (δ := 2693/250000000) (ψ := -431649/1000000) 212 177
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t187 : ((-330128076939/5000000000000 : ℚ) : ℝ) ≤ stT212 187 := by
  have hc : ((-451443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-330128076939/5000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-451443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c188 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((217/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1958071/5000000) (δ := 2693/250000000) (ψ := -431649/1000000) 212 177
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t188 : ((78219999/250000000000 : ℚ) : ℝ) ≤ stT212 188 := by
  have hc : ((429/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78219999/250000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((429/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c189 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((451997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1104439/10000000) (δ := 2693/250000000) (ψ := -431649/1000000) 212 177
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t189 : ((2568443883/39062500000 : ℚ) : ℝ) ≤ stT212 189 := by
  have hc : ((112993/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2568443883/39062500000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((112993/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c190 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((24359/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1692371/10000000) (δ := 2693/250000000) (ψ := -431649/1000000) 212 177
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t190 : ((70682945311/1250000000000 : ℚ) : ℝ) ≤ stT212 190 := by
  have hc : ((389719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70682945311/1250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((389719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c191 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-108639/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4474553/10000000) (δ := 2693/250000000) (ψ := -431649/1000000) 212 177
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t191 : ((-393132769/25000000000 : ℚ) : ℝ) ≤ stT212 191 := by
  have hc : ((-13583/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-393132769/25000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-13583/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c192 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-970203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 90527/125000) (δ := 2693/250000000) (ψ := -431649/1000000) 212 177
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t192 : ((-87527493383/1250000000000 : ℚ) : ℝ) ≤ stT212 192 := by
  have hc : ((-970253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87527493383/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-970253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c193 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-327517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71407/125000) (δ := 2681/250000000) (ψ := -431649/1000000) 212 178
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t193 : ((-14735623267/312500000000 : ℚ) : ℝ) ≤ stT212 193 := by
  have hc : ((-163771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14735623267/312500000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-163771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c194 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((372209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37169/125000) (δ := 2681/250000000) (ψ := -431649/1000000) 212 178
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t194 : ((133597265661/5000000000000 : ℚ) : ℝ) ≤ stT212 194 := by
  have hc : ((372159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133597265661/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((372159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c195 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((995061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -124289/5000000) (δ := 2681/250000000) (ψ := -431649/1000000) 212 178
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t195 : ((356270653627/5000000000000 : ℚ) : ℝ) ≤ stT212 195 := by
  have hc : ((995011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((356270653627/5000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((995011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c196 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((69111/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98497/400000) (δ := 2681/250000000) (ψ := -431649/1000000) 212 178
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t196 : ((39488389083/1000000000000 : ℚ) : ℝ) ≤ stT212 196 := by
  have hc : ((276419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39488389083/1000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((276419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c197 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-236663/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 161239/312500) (δ := 2681/250000000) (ψ := -431649/1000000) 212 178
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t197 : ((-10539583503/312500000000 : ℚ) : ℝ) ≤ stT212 197 := by
  have hc : ((-14793/31250 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10539583503/312500000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-14793/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c198 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-999991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7843197/10000000) (δ := 2681/250000000) (ψ := -431649/1000000) 212 178
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t198 : ((-71069913747/1000000000000 : ℚ) : ℝ) ≤ stT212 198 := by
  have hc : ((-1000041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71069913747/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-1000041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c199 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-485641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1298683/2500000) (δ := 1327/125000000) (ψ := -431649/1000000) 212 179
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t199 : ((-172148803731/5000000000000 : ℚ) : ℝ) ≤ stT212 199 := by
  have hc : ((-485691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172148803731/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-485691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c200 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((263707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2538107/10000000) (δ := 1327/125000000) (ψ := -431649/1000000) 212 179
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t200 : ((46612781073/1250000000000 : ℚ) : ℝ) ≤ stT212 200 := by
  have hc : ((131841/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46612781073/1250000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((131841/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c201 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((999113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 105321/10000000) (δ := 1327/125000000) (ψ := -431649/1000000) 212 179
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t201 : ((140936818347/2000000000000 : ℚ) : ℝ) ≤ stT212 201 := by
  have hc : ((999063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140936818347/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((999063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c202 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((458739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42743/156250) (δ := 1327/125000000) (ψ := -431649/1000000) 212 179
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t202 : ((322732204333/10000000000000 : ℚ) : ℝ) ≤ stT212 202 := by
  have hc : ((458689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((322732204333/10000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((458689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c203 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-269961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5352851/10000000) (δ := 1327/125000000) (ψ := -431649/1000000) 212 179
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t203 : ((-94746591959/2500000000000 : ℚ) : ℝ) ≤ stT212 203 := by
  have hc : ((-134993/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94746591959/2500000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-134993/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c204 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-999147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1937673/2500000) (δ := 5347/500000000) (ψ := -431649/1000000) 212 180
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t204 : ((-699578786777/10000000000000 : ℚ) : ℝ) ≤ stT212 204 := by
  have hc : ((-999197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-699578786777/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-999197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c205 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-94619/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -322437/625000) (δ := 5347/500000000) (ψ := -431649/1000000) 212 180
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t205 : ((-66091827099/2000000000000 : ℚ) : ℝ) ≤ stT212 205 := by
  have hc : ((-94629/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66091827099/2000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-94629/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c206 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((102627/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1289953/5000000) (δ := 5347/500000000) (ψ := -431649/1000000) 212 180
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t206 : ((71496650261/2000000000000 : ℚ) : ℝ) ≤ stT212 206 := by
  have hc : ((102617/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71496650261/2000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((102617/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c207 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((499993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -833/625000) (δ := 5347/500000000) (ψ := -431649/1000000) 212 180
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t207 : ((169678593/2441406250 : ℚ) : ℝ) ≤ stT212 207 := by
  have hc : ((15624/15625 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169678593/2441406250 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((15624/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c208 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((8226/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2540901/10000000) (δ := 5347/500000000) (ψ := -431649/1000000) 212 180
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t208 : ((1460009229/40000000000 : ℚ) : ℝ) ≤ stT212 208 := by
  have hc : ((263207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1460009229/40000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((263207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c209 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-22303/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5082887/10000000) (δ := 5347/500000000) (ψ := -431649/1000000) 212 180
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t209 : ((-6171619573/200000000000 : ℚ) : ℝ) ≤ stT212 209 := by
  have hc : ((-44611/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6171619573/200000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-44611/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c210 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-248837/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 118949/156250) (δ := 5347/500000000) (ψ := -431649/1000000) 212 180
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t210 : ((-171722579067/2500000000000 : ℚ) : ℝ) ≤ stT212 210 := by
  have hc : ((-497699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171722579067/2500000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-497699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c211 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-613249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5577409/10000000) (δ := 10801/1000000000) (ψ := -431649/1000000) 212 181
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t211 : ((-422212817271/10000000000000 : ℚ) : ℝ) ≤ stT212 211 := by
  have hc : ((-613299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-422212817271/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-613299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c212 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((335551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -767879/2500000) (δ := 10801/1000000000) (ψ := -431649/1000000) 212 181
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t212 : ((115211378901/5000000000000 : ℚ) : ℝ) ≤ stT212 212 := by
  have hc : ((335501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115211378901/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((335501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c213 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((121681/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -577389/10000000) (δ := 10801/1000000000) (ψ := -431649/1000000) 212 181
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t213 : ((83370078603/1250000000000 : ℚ) : ℝ) ≤ stT212 213 := by
  have hc : ((486699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83370078603/1250000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((486699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c214 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((144687/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 952539/5000000) (δ := 10801/1000000000) (ψ := -431649/1000000) 212 181
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t214 : ((19779805409/400000000000 : ℚ) : ℝ) ≤ stT212 214 := by
  have hc : ((144677/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19779805409/400000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((144677/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c215 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-35723/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2187969/5000000) (δ := 10801/1000000000) (ψ := -431649/1000000) 212 181
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t215 : ((-4873945467/400000000000 : ℚ) : ℝ) ≤ stT212 215 := by
  have hc : ((-35733/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4873945467/400000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-35733/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c216 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-918133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 136707/200000) (δ := 10801/1000000000) (ψ := -431649/1000000) 212 181
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t216 : ((-312372283881/5000000000000 : ℚ) : ℝ) ≤ stT212 216 := by
  have hc : ((-918183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-312372283881/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-918183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c217 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-840953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6424597/10000000) (δ := 2139/200000000) (ψ := -431649/1000000) 212 182
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t217 : ((-114182136307/2000000000000 : ℚ) : ℝ) ≤ stT212 217 := by
  have hc : ((-841003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114182136307/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-841003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c218 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-3041/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -498477/1250000) (δ := 2139/200000000) (ψ := -431649/1000000) 212 182
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t218 : ((-4127719527/2500000000000 : ℚ) : ℝ) ≤ stT212 218 := by
  have hc : ((-12189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4127719527/2500000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-12189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c219 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((405521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -312433/2000000) (δ := 2139/200000000) (ψ := -431649/1000000) 212 182
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t219 : ((34251081319/625000000000 : ℚ) : ℝ) ≤ stT212 219 := by
  have hc : ((50687/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34251081319/625000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((50687/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c220 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((942433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 852409/10000000) (δ := 2139/200000000) (ψ := -431649/1000000) 212 182
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t220 : ((635353676217/10000000000000 : ℚ) : ℝ) ≤ stT212 220 := by
  have hc : ((942383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((635353676217/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((942383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c221 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((6629/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 651213/2000000) (δ := 2139/200000000) (ψ := -431649/1000000) 212 182
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t221 : ((557287731/31250000000 : ℚ) : ℝ) ≤ stT212 221 := by
  have hc : ((26511/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((557287731/31250000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((26511/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c222 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-635553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5648803/10000000) (δ := 2139/200000000) (ψ := -431649/1000000) 212 182
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t222 : ((-426589402671/10000000000000 : ℚ) : ℝ) ≤ stT212 222 := by
  have hc : ((-635603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426589402671/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-635603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c223 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-997499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -959641/1250000) (δ := 2123/200000000) (ψ := -431649/1000000) 212 183
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t223 : ((-13360173757/200000000000 : ℚ) : ℝ) ≤ stT212 223 := by
  have hc : ((-997549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13360173757/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-997549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c224 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-8187/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5305749/10000000) (δ := 2123/200000000) (ψ := -431649/1000000) 212 183
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t224 : ((-87531180693/2500000000000 : ℚ) : ℝ) ≤ stT212 224 := by
  have hc : ((-262009/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87531180693/2500000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-262009/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c225 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((95701/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2944917/10000000) (δ := 2123/200000000) (ψ := -431649/1000000) 212 183
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t225 : ((63792269541/2500000000000 : ℚ) : ℝ) ≤ stT212 225 := by
  have hc : ((191377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63792269541/2500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((191377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c226 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((971849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -297303/5000000) (δ := 5347/250000000) (ψ := -431649/1000000) 212 183
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t226 : ((64643097681/1000000000000 : ℚ) : ℝ) ≤ stT212 226 := by
  have hc : ((971799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64643097681/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((971799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c227 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((383017/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1745371/10000000) (δ := 2123/200000000) (ψ := -431649/1000000) 212 183
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t227 : ((15887537451/312500000000 : ℚ) : ℝ) ≤ stT212 227 := by
  have hc : ((23937/31250 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15887537451/312500000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((23937/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c228 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-11837/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4075039/10000000) (δ := 2123/200000000) (ψ := -431649/1000000) 212 183
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t228 : ((-7845877149/2000000000000 : ℚ) : ℝ) ≤ stT212 228 := by
  have hc : ((-11847/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7845877149/2000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-11847/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c229 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-166877/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6394531/10000000) (δ := 2123/200000000) (ψ := -431649/1000000) 212 183
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t229 : ((-110282100453/2000000000000 : ℚ) : ℝ) ≤ stT212 229 := by
  have hc : ((-166887/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110282100453/2000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-166887/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c230 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-471383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7004063/10000000) (δ := 10723/1000000000) (ψ := -431649/1000000) 212 184
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t230 : ((-19427342403/312500000000 : ℚ) : ℝ) ≤ stT212 230 := by
  have hc : ((-29463/31250 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19427342403/312500000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-29463/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c231 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-61219/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4704711/10000000) (δ := 10723/1000000000) (ψ := -431649/1000000) 212 184
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t231 : ((-1258929469/62500000000 : ℚ) : ℝ) ≤ stT212 231 := by
  have hc : ((-61229/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1258929469/62500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-61229/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c232 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((71061/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2415323/10000000) (δ := 10723/1000000000) (ψ := -431649/1000000) 212 184
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t232 : ((46649717127/1250000000000 : ℚ) : ℝ) ≤ stT212 232 := by
  have hc : ((284219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46649717127/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((284219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c233 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((499263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6787/500000) (δ := 10723/1000000000) (ψ := -431649/1000000) 212 184
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t233 : ((163530648899/2500000000000 : ℚ) : ℝ) ≤ stT212 233 := by
  have hc : ((249619/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163530648899/2500000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((249619/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c234 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((657247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2134091/10000000) (δ := 10723/1000000000) (ψ := -431649/1000000) 212 184
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t234 : ((10740570571/250000000000 : ℚ) : ℝ) ≤ stT212 234 := by
  have hc : ((657197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10740570571/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((657197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c235 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-185807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4394223/10000000) (δ := 10723/1000000000) (ψ := -431649/1000000) 212 184
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t235 : ((-121239910953/10000000000000 : ℚ) : ℝ) ≤ stT212 235 := by
  have hc : ((-185857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121239910953/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-185857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c236 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-442643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3322381/5000000) (δ := 10723/1000000000) (ψ := -431649/1000000) 212 184
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t236 : ((-14407626063/250000000000 : ℚ) : ℝ) ≤ stT212 236 := by
  have hc : ((-110667/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14407626063/250000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-110667/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c237 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-916037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6822203/10000000) (δ := 10773/1000000000) (ψ := -431649/1000000) 212 185
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t237 : ((-59506263259/1000000000000 : ℚ) : ℝ) ≤ stT212 237 := by
  have hc : ((-916087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59506263259/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-916087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c238 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-16397/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2295319/5000000) (δ := 10773/1000000000) (ψ := -431649/1000000) 212 185
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t238 : ((-21261253251/1250000000000 : ℚ) : ℝ) ≤ stT212 238 := by
  have hc : ((-131201/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21261253251/1250000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-131201/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c239 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((145957/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2368401/10000000) (δ := 10773/1000000000) (ψ := -431649/1000000) 212 185
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t239 : ((94403616047/2500000000000 : ℚ) : ℝ) ≤ stT212 239 := by
  have hc : ((291889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94403616047/2500000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((291889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c240 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((249517/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -155439/10000000) (δ := 10773/1000000000) (ψ := -431649/1000000) 212 185
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t240 : ((322108812473/5000000000000 : ℚ) : ℝ) ≤ stT212 240 := by
  have hc : ((499009/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((322108812473/5000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((499009/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c241 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((341359/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2048301/10000000) (δ := 10773/1000000000) (ψ := -431649/1000000) 212 185
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t241 : ((27484043013/625000000000 : ℚ) : ℝ) ≤ stT212 241 := by
  have hc : ((170667/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27484043013/625000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((170667/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c242 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-63019/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 169717/400000) (δ := 10773/1000000000) (ψ := -431649/1000000) 212 185
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t242 : ((-405262593/50000000000 : ℚ) : ℝ) ≤ stT212 242 := by
  have hc : ((-15761/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-405262593/50000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-15761/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c243 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-420897/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3214243/5000000) (δ := 10773/1000000000) (ψ := -431649/1000000) 212 185
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t243 : ((-135010941961/2500000000000 : ℚ) : ℝ) ≤ stT212 243 := by
  have hc : ((-210461/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135010941961/2500000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-210461/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c244 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-191041/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7102873/10000000) (δ := 5333/500000000) (ψ := -431649/1000000) 212 186
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t244 : ((-24461596887/400000000000 : ℚ) : ℝ) ≤ stT212 244 := by
  have hc : ((-191051/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24461596887/400000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-191051/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c245 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-9811/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4935199/10000000) (δ := 21337/1000000000) (ψ := -431649/1000000) 212 186
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t245 : ((-25075283373/1000000000000 : ℚ) : ℝ) ≤ stT212 245 := by
  have hc : ((-39249/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25075283373/1000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-39249/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c246 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((444187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -694081/2500000) (δ := 5333/500000000) (ψ := -431649/1000000) 212 186
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t246 : ((35396386489/1250000000000 : ℚ) : ℝ) ≤ stT212 246 := by
  have hc : ((444137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35396386489/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((444137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c247 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((121099/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -31311/500000) (δ := 5333/500000000) (ψ := -431649/1000000) 212 186
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t247 : ((77049379341/1250000000000 : ℚ) : ℝ) ≤ stT212 247 := by
  have hc : ((484371/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77049379341/1250000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((484371/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c248 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((821889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 189399/1250000) (δ := 5333/500000000) (ψ := -431649/1000000) 212 186
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t248 : ((104373553/2000000000 : ℚ) : ℝ) ≤ stT212 248 := by
  have hc : ((821839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104373553/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((821839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c249 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((111379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 729593/2000000) (δ := 5333/500000000) (ψ := -431649/1000000) 212 186
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t249 : ((17637964799/2500000000000 : ℚ) : ℝ) ≤ stT212 249 := by
  have hc : ((111329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17637964799/2500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((111329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c250 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-672889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2886129/5000000) (δ := 5333/500000000) (ψ := -431649/1000000) 212 186
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t250 : ((-53200538523/1250000000000 : ℚ) : ℝ) ≤ stT212 250 := by
  have hc : ((-672939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53200538523/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-672939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c251 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-999907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1563989/2000000) (δ := 2661/250000000) (ψ := -431649/1000000) 212 187
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t251 : ((-126233571723/2000000000000 : ℚ) : ℝ) ≤ stT212 251 := by
  have hc : ((-999957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).2
  have h0 : (0:ℝ) ≤ ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126233571723/2000000000000 : ℚ) : ℝ)
      = ((126239/2000000 : ℚ) : ℝ) * ((-999957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c252 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-13101/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1428153/2500000) (δ := 2661/250000000) (ψ := -431649/1000000) 212 187
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t252 : ((-4126743491/100000000000 : ℚ) : ℝ) ≤ stT212 252 := by
  have hc : ((-6551/10000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4126743491/100000000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-6551/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c253 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((31257/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4517/12500) (δ := 2661/250000000) (ψ := -431649/1000000) 212 187
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t253 : ((19643229683/2500000000000 : ℚ) : ℝ) ≤ stT212 253 := by
  have hc : ((62489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).1
  have hw2 : ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((314347/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19643229683/2500000000000 : ℚ) : ℝ)
      = ((314347/5000000 : ℚ) : ℝ) * ((62489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c254 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((820139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -190357/1250000) (δ := 2661/250000000) (ψ := -431649/1000000) 212 187
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t254 : ((102913788699/2000000000000 : ℚ) : ℝ) ≤ stT212 254 := by
  have hc : ((820089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).1
  have hw2 : ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((125491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102913788699/2000000000000 : ℚ) : ℝ)
      = ((125491/2000000 : ℚ) : ℝ) * ((820089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c255 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((487523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 559673/10000000) (δ := 2661/250000000) (ψ := -431649/1000000) 212 187
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t255 : ((9540092111/156250000000 : ℚ) : ℝ) ≤ stT212 255 := by
  have hc : ((243749/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).1
  have hw2 : ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39139/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9540092111/156250000000 : ℚ) : ℝ)
      = ((39139/625000 : ℚ) : ℝ) * ((243749/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c256 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((494431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65851/250000) (δ := 2661/250000000) (ψ := -431649/1000000) 212 187
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t256 : ((494381/16000000 : ℚ) : ℝ) ≤ stT212 256 := by
  have hc : ((494381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((494381/16000000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((494381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c257 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-152207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2350149/5000000) (δ := 2661/250000000) (ψ := -431649/1000000) 212 187
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t257 : ((-11869966707/625000000000 : ℚ) : ℝ) ≤ stT212 257 := by
  have hc : ((-19029/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).2
  have h0 : (0:ℝ) ≤ ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11869966707/625000000000 : ℚ) : ℝ)
      = ((623783/10000000 : ℚ) : ℝ) * ((-19029/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c258 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-905529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6758553/10000000) (δ := 2661/250000000) (ψ := -431649/1000000) 212 187
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t258 : ((-563789034767/10000000000000 : ℚ) : ℝ) ≤ stT212 258 := by
  have hc : ((-905579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).2
  have h0 : (0:ℝ) ≤ ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-563789034767/10000000000000 : ℚ) : ℝ)
      = ((622573/10000000 : ℚ) : ℝ) * ((-905579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c259 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-927939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1379821/2000000) (δ := 10751/1000000000) (ψ := -431649/1000000) 212 188
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t259 : ((-57662452493/1000000000000 : ℚ) : ℝ) ≤ stT212 259 := by
  have hc : ((-927989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57662452493/1000000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-927989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c260 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-36337/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4856697/10000000) (δ := 10751/1000000000) (ψ := -431649/1000000) 212 188
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t260 : ((-5634590877/250000000000 : ℚ) : ℝ) ≤ stT212 260 := by
  have hc : ((-18171/50000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5634590877/250000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-18171/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c261 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((427697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2822133/10000000) (δ := 10751/1000000000) (ψ := -431649/1000000) 212 188
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t261 : ((33088331331/1250000000000 : ℚ) : ℝ) ≤ stT212 261 := by
  have hc : ((427647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).1
  have hw2 : ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((77373/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33088331331/1250000000000 : ℚ) : ℝ)
      = ((77373/1250000 : ℚ) : ℝ) * ((427647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c262 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((474909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4971/62500) (δ := 31951/1000000000) (ψ := -431649/1000000) 212 188
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t262 : ((36673035621/625000000000 : ℚ) : ℝ) ≤ stT212 262 := by
  have hc : ((118721/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).1
  have hw2 : ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36673035621/625000000000 : ℚ) : ℝ)
      = ((308901/5000000 : ℚ) : ℝ) * ((118721/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c263 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((441291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 48947/400000) (δ := 10751/1000000000) (ψ := -431649/1000000) 212 188
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t263 : ((68024022129/1250000000000 : ℚ) : ℝ) ≤ stT212 263 := by
  have hc : ((220633/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68024022129/1250000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((220633/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c264 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((54649/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1617539/5000000) (δ := 31951/1000000000) (ψ := -431649/1000000) 212 188
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t264 : ((33627955023/2000000000000 : ℚ) : ℝ) ≤ stT212 264 := by
  have hc : ((54639/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33627955023/2000000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((54639/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c265 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-500991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5238849/10000000) (δ := 10751/1000000000) (ψ := -431649/1000000) 212 188
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t265 : ((-38473435267/1250000000000 : ℚ) : ℝ) ≤ stT212 265 := by
  have hc : ((-501041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).2
  have h0 : (0:ℝ) ≤ ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38473435267/1250000000000 : ℚ) : ℝ)
      = ((76787/1250000 : ℚ) : ℝ) * ((-501041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c266 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-484757/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3617547/5000000) (δ := 10751/1000000000) (ψ := -431649/1000000) 212 188
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t266 : ((-7430980887/125000000000 : ℚ) : ℝ) ≤ stT212 266 := by
  have hc : ((-242391/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7430980887/125000000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-242391/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c267 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-853603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6484151/10000000) (δ := 2149/200000000) (ψ := -431649/1000000) 212 189
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t267 : ((-522427953123/10000000000000 : ℚ) : ℝ) ≤ stT212 267 := by
  have hc : ((-853653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-522427953123/10000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-853653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c268 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-228313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1125713/2500000) (δ := 2149/200000000) (ψ := -431649/1000000) 212 189
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t268 : ((-4359221307/312500000000 : ℚ) : ℝ) ≤ stT212 268 := by
  have hc : ((-228363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4359221307/312500000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-228363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c269 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((132633/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63223/250000) (δ := 2149/200000000) (ψ := -431649/1000000) 212 189
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t269 : ((16172009011/500000000000 : ℚ) : ℝ) ≤ stT212 269 := by
  have hc : ((265241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16172009011/500000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((265241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c270 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((243703/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -281151/5000000) (δ := 2149/200000000) (ψ := -431649/1000000) 212 189
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t270 : ((14830516449/250000000000 : ℚ) : ℝ) ≤ stT212 270 := by
  have hc : ((487381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14830516449/250000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((487381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c271 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((21197/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 279411/2000000) (δ := 2149/200000000) (ψ := -431649/1000000) 212 189
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t271 : ((1609435689/31250000000 : ℚ) : ℝ) ≤ stT212 271 := by
  have hc : ((84783/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1609435689/31250000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((84783/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c272 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((229083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3349151/10000000) (δ := 2149/200000000) (ψ := -431649/1000000) 212 189
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t272 : ((138871640187/10000000000000 : ℚ) : ℝ) ≤ stT212 272 := by
  have hc : ((229033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138871640187/10000000000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((229033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c273 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-519991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1323523/2500000) (δ := 2149/200000000) (ψ := -431649/1000000) 212 189
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t273 : ((-78685843587/2500000000000 : ℚ) : ℝ) ≤ stT212 273 := by
  have hc : ((-520041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78685843587/2500000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-520041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c274 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-969209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 451999/625000) (δ := 2149/200000000) (ψ := -431649/1000000) 212 189
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t274 : ((-585551654857/10000000000000 : ℚ) : ℝ) ≤ stT212 274 := by
  have hc : ((-969259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-585551654857/10000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-969259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c275 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-866077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3272621/5000000) (δ := 10637/1000000000) (ψ := -431649/1000000) 212 190
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t275 : ((-522294501921/10000000000000 : ℚ) : ℝ) ≤ stT212 275 := by
  have hc : ((-866127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-522294501921/10000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-866127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c276 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-17139/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -577681/1250000) (δ := 10637/1000000000) (ψ := -431649/1000000) 212 190
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t276 : ((-8254687441/500000000000 : ℚ) : ℝ) ≤ stT212 276 := by
  have hc : ((-137137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).2
  have h0 : (0:ℝ) ≤ ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8254687441/500000000000 : ℚ) : ℝ)
      = ((60193/1000000 : ℚ) : ℝ) * ((-137137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c277 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((234853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2704597/10000000) (δ := 10637/1000000000) (ψ := -431649/1000000) 212 190
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t277 : ((35273572587/1250000000000 : ℚ) : ℝ) ≤ stT212 277 := by
  have hc : ((58707/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35273572587/1250000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((58707/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c278 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((474951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -794689/10000000) (δ := 10637/1000000000) (ψ := -431649/1000000) 212 190
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t278 : ((1780260111/31250000000 : ℚ) : ℝ) ≤ stT212 278 := by
  have hc : ((237463/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1780260111/31250000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((237463/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c279 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((28229/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1108329/10000000) (δ := 10637/1000000000) (ψ := -431649/1000000) 212 190
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t279 : ((67597260769/1250000000000 : ℚ) : ℝ) ≤ stT212 279 := by
  have hc : ((451639/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).1
  have hw2 : ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149671/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67597260769/1250000000000 : ℚ) : ℝ)
      = ((149671/2500000 : ℚ) : ℝ) * ((451639/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c280 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((90159/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 375577/1250000) (δ := 10637/1000000000) (ψ := -431649/1000000) 212 190
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t280 : ((53872810451/2500000000000 : ℚ) : ℝ) ≤ stT212 280 := by
  have hc : ((180293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).1
  have hw2 : ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53872810451/2500000000000 : ℚ) : ℝ)
      = ((298807/5000000 : ℚ) : ℝ) * ((180293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c281 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-75451/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2447033/5000000) (δ := 10637/1000000000) (ψ := -431649/1000000) 212 190
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t281 : ((-900325191/40000000000 : ℚ) : ℝ) ≤ stT212 281 := by
  have hc : ((-75461/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-900325191/40000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-75461/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c282 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-14197/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3388419/5000000) (δ := 10637/1000000000) (ψ := -431649/1000000) 212 190
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t282 : ((-67637321217/1250000000000 : ℚ) : ℝ) ≤ stT212 282 := by
  have hc : ((-454329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).2
  have h0 : (0:ℝ) ≤ ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67637321217/1250000000000 : ℚ) : ℝ)
      = ((148873/2500000 : ℚ) : ℝ) * ((-454329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c283 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-949367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7055031/10000000) (δ := 10673/1000000000) (ψ := -431649/1000000) 212 191
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t283 : ((-564370492063/10000000000000 : ℚ) : ℝ) ≤ stT212 283 := by
  have hc : ((-949417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).2
  have h0 : (0:ℝ) ≤ ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-564370492063/10000000000000 : ℚ) : ℝ)
      = ((594439/10000000 : ℚ) : ℝ) * ((-949417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c284 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-482413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5185509/10000000) (δ := 10673/1000000000) (ψ := -431649/1000000) 212 191
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t284 : ((-286289202033/10000000000000 : ℚ) : ℝ) ≤ stT212 284 := by
  have hc : ((-482463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).2
  have h0 : (0:ℝ) ≤ ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286289202033/10000000000000 : ℚ) : ℝ)
      = ((593391/10000000 : ℚ) : ℝ) * ((-482463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c285 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((59851/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -830653/2500000) (δ := 10673/1000000000) (ψ := -431649/1000000) 212 191
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t285 : ((17722607899/1250000000000 : ℚ) : ℝ) ≤ stT212 285 := by
  have hc : ((119677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).1
  have hw2 : ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((148087/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17722607899/1250000000000 : ℚ) : ℝ)
      = ((148087/2500000 : ℚ) : ℝ) * ((119677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c286 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((416449/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1466181/10000000) (δ := 10673/1000000000) (ψ := -431649/1000000) 212 191
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t286 : ((1923722721/39062500000 : ℚ) : ℝ) ≤ stT212 286 := by
  have hc : ((52053/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).1
  have hw2 : ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((36957/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1923722721/39062500000 : ℚ) : ℝ)
      = ((36957/625000 : ℚ) : ℝ) * ((52053/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c287 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((988243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 383731/10000000) (δ := 10673/1000000000) (ψ := -431649/1000000) 212 191
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t287 : ((583311552233/10000000000000 : ℚ) : ℝ) ≤ stT212 287 := by
  have hc : ((988193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).1
  have hw2 : ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((590281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((583311552233/10000000000000 : ℚ) : ℝ)
      = ((590281/10000000 : ℚ) : ℝ) * ((988193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c288 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((125747/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2227177/10000000) (δ := 10673/1000000000) (ψ := -431649/1000000) 212 191
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t288 : ((14818231187/400000000000 : ℚ) : ℝ) ≤ stT212 288 := by
  have hc : ((125737/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14818231187/400000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((125737/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c289 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-54881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4064263/10000000) (δ := 10673/1000000000) (ψ := -431649/1000000) 212 191
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t289 : ((-8078097929/2500000000000 : ℚ) : ℝ) ≤ stT212 289 := by
  have hc : ((-54931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).2
  have h0 : (0:ℝ) ≤ ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8078097929/2500000000000 : ℚ) : ℝ)
      = ((147059/2500000 : ℚ) : ℝ) * ((-54931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c290 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-354197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2947521/5000000) (δ := 10673/1000000000) (ψ := -431649/1000000) 212 191
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t290 : ((-104003298531/2500000000000 : ℚ) : ℝ) ≤ stT212 290 := by
  have hc : ((-177111/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).2
  have h0 : (0:ℝ) ≤ ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104003298531/2500000000000 : ℚ) : ℝ)
      = ((587221/10000000 : ℚ) : ℝ) * ((-177111/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c291 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-998553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7719461/10000000) (δ := 10673/1000000000) (ψ := -431649/1000000) 212 191
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t291 : ((-585392063233/10000000000000 : ℚ) : ℝ) ≤ stT212 291 := by
  have hc : ((-998603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).2
  have h0 : (0:ℝ) ≤ ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-585392063233/10000000000000 : ℚ) : ℝ)
      = ((586211/10000000 : ℚ) : ℝ) * ((-998603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c292 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-97707/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1542571/2500000) (δ := 539/50000000) (ψ := -431649/1000000) 212 192
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t292 : ((-114364760359/2500000000000 : ℚ) : ℝ) ≤ stT212 292 := by
  have hc : ((-390853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114364760359/2500000000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-390853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c293 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-171677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54479/125000) (δ := 539/50000000) (ψ := -431649/1000000) 212 192
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t293 : ((-100324115489/10000000000000 : ℚ) : ℝ) ≤ stT212 293 := by
  have hc : ((-171727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100324115489/10000000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-171727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c294 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((261247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2552557/10000000) (δ := 539/50000000) (ψ := -431649/1000000) 212 192
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t294 : ((76173771921/2500000000000 : ℚ) : ℝ) ≤ stT212 294 := by
  have hc : ((130611/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).1
  have hw2 : ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((583211/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76173771921/2500000000000 : ℚ) : ℝ)
      = ((583211/10000000 : ℚ) : ℝ) * ((130611/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c295 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((477497/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -752889/10000000) (δ := 539/50000000) (ψ := -431649/1000000) 212 192
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t295 : ((4343667231/78125000000 : ℚ) : ℝ) ≤ stT212 295 := by
  have hc : ((14921/15625 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).1
  have hw2 : ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((291111/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4343667231/78125000000 : ℚ) : ℝ)
      = ((291111/5000000 : ℚ) : ℝ) * ((14921/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c296 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((457301/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 260171/2500000) (δ := 539/50000000) (ψ := -431649/1000000) 212 192
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t296 : ((33223273461/625000000000 : ℚ) : ℝ) ≤ stT212 296 := by
  have hc : ((114319/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).1
  have hw2 : ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33223273461/625000000000 : ℚ) : ℝ)
      = ((290619/5000000 : ℚ) : ℝ) * ((114319/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c297 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((53187/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 565643/2000000) (δ := 539/50000000) (ψ := -431649/1000000) 212 192
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t297 : ((61717111267/2500000000000 : ℚ) : ℝ) ≤ stT212 297 := by
  have hc : ((212723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).1
  have hw2 : ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290129/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61717111267/2500000000000 : ℚ) : ℝ)
      = ((290129/5000000 : ℚ) : ℝ) * ((212723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c298 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-33713/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 576213/1250000) (δ := 539/50000000) (ψ := -431649/1000000) 212 192
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t298 : ((-15626444589/1000000000000 : ℚ) : ℝ) ≤ stT212 298 := by
  have hc : ((-134877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).2
  have h0 : (0:ℝ) ≤ ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15626444589/1000000000000 : ℚ) : ℝ)
      = ((115857/2000000 : ℚ) : ℝ) * ((-134877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c299 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-166467/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6385257/10000000) (δ := 539/50000000) (ψ := -431649/1000000) 212 192
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t299 : ((-19255229251/400000000000 : ℚ) : ℝ) ≤ stT212 299 := by
  have hc : ((-166477/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).2
  have h0 : (0:ℝ) ≤ ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19255229251/400000000000 : ℚ) : ℝ)
      = ((115663/2000000 : ℚ) : ℝ) * ((-166477/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c300 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-496383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -755309/1000000) (δ := 2679/250000000) (ψ := -431649/1000000) 212 193
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t300 : ((-35825206901/625000000000 : ℚ) : ℝ) ≤ stT212 300 := by
  have hc : ((-62051/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).2
  have h0 : (0:ℝ) ≤ ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35825206901/625000000000 : ℚ) : ℝ)
      = ((577351/10000000 : ℚ) : ℝ) * ((-62051/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c301 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-169483/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1447339/2500000) (δ := 2679/250000000) (ψ := -431649/1000000) 212 193
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t301 : ((-195391361481/5000000000000 : ℚ) : ℝ) ≤ stT212 301 := by
  have hc : ((-338991/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).2
  have h0 : (0:ℝ) ≤ ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195391361481/5000000000000 : ℚ) : ℝ)
      = ((576391/10000000 : ℚ) : ℝ) * ((-338991/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c302 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-10443/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1007863/2500000) (δ := 2679/250000000) (ψ := -431649/1000000) 212 193
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t302 : ((-3008235549/1250000000000 : ℚ) : ℝ) ≤ stT212 302 := by
  have hc : ((-20911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3008235549/1250000000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-20911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c303 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((306181/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1139689/5000000) (δ := 2679/250000000) (ψ := -431649/1000000) 212 193
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t303 : ((10992607719/312500000000 : ℚ) : ℝ) ≤ stT212 303 := by
  have hc : ((76539/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).1
  have hw2 : ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143621/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10992607719/312500000000 : ℚ) : ℝ)
      = ((143621/2500000 : ℚ) : ℝ) * ((76539/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c304 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((122169/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -533081/10000000) (δ := 2679/250000000) (ψ := -431649/1000000) 212 193
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t304 : ((280260405889/5000000000000 : ℚ) : ℝ) ≤ stT212 304 := by
  have hc : ((488651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).1
  have hw2 : ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((280260405889/5000000000000 : ℚ) : ℝ)
      = ((573539/10000000 : ℚ) : ℝ) * ((488651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c305 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((885617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1207439/10000000) (δ := 2679/250000000) (ψ := -431649/1000000) 212 193
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t305 : ((253536946533/5000000000000 : ℚ) : ℝ) ≤ stT212 305 := by
  have hc : ((885567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((253536946533/5000000000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((885567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c306 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((95939/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2942341/10000000) (δ := 2679/250000000) (ψ := -431649/1000000) 212 193
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t306 : ((109674877833/5000000000000 : ℚ) : ℝ) ≤ stT212 306 := by
  have hc : ((191853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109674877833/5000000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((191853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c307 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-293429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4671519/10000000) (δ := 2679/250000000) (ψ := -431649/1000000) 212 193
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t307 : ((-167497563149/10000000000000 : ℚ) : ℝ) ≤ stT212 307 := by
  have hc : ((-293479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).2
  have h0 : (0:ℝ) ≤ ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167497563149/10000000000000 : ℚ) : ℝ)
      = ((570731/10000000 : ℚ) : ℝ) * ((-293479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c308 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-417253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6395079/10000000) (δ := 2679/250000000) (ψ := -431649/1000000) 212 193
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t308 : ((-118883128117/2500000000000 : ℚ) : ℝ) ≤ stT212 308 := by
  have hc : ((-208639/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).2
  have h0 : (0:ℝ) ≤ ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118883128117/2500000000000 : ℚ) : ℝ)
      = ((569803/10000000 : ℚ) : ℝ) * ((-208639/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c309 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-497317/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7594889/10000000) (δ := 10609/1000000000) (ψ := -431649/1000000) 212 194
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t309 : ((-141464207151/2500000000000 : ℚ) : ℝ) ≤ stT212 309 := by
  have hc : ((-248671/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).2
  have h0 : (0:ℝ) ≤ ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141464207151/2500000000000 : ℚ) : ℝ)
      = ((568881/10000000 : ℚ) : ℝ) * ((-248671/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c310 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-704833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5882459/10000000) (δ := 10609/1000000000) (ψ := -431649/1000000) 212 194
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t310 : ((-200173379223/5000000000000 : ℚ) : ℝ) ≤ stT212 310 := by
  have hc : ((-704883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200173379223/5000000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-704883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c311 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-19847/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32621/78125) (δ := 10609/1000000000) (ψ := -431649/1000000) 212 194
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t311 : ((-1407484017/250000000000 : ℚ) : ℝ) ≤ stT212 311 := by
  have hc : ((-19857/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1407484017/250000000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-19857/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c312 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((548997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1237041/5000000) (δ := 10609/1000000000) (ψ := -431649/1000000) 212 194
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t312 : ((155389878343/5000000000000 : ℚ) : ℝ) ≤ stT212 312 := by
  have hc : ((548947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).1
  have hw2 : ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((283069/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155389878343/5000000000000 : ℚ) : ℝ)
      = ((283069/5000000 : ℚ) : ℝ) * ((548947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c313 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((951957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -389041/5000000) (δ := 10609/1000000000) (ψ := -431649/1000000) 212 194
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t313 : ((538049249331/10000000000000 : ℚ) : ℝ) ≤ stT212 313 := by
  have hc : ((951907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).1
  have hw2 : ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((565233/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((538049249331/10000000000000 : ℚ) : ℝ)
      = ((565233/10000000 : ℚ) : ℝ) * ((951907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c314 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((467061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7129/78125) (δ := 10609/1000000000) (ψ := -431649/1000000) 212 194
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t314 : ((16472709997/312500000000 : ℚ) : ℝ) ≤ stT212 314 := by
  have hc : ((116759/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16472709997/312500000000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((116759/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c315 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((101399/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2597753/10000000) (δ := 10609/1000000000) (ψ := -431649/1000000) 212 194
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t315 : ((14281553151/500000000000 : ℚ) : ℝ) ≤ stT212 315 := by
  have hc : ((101389/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14281553151/500000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((101389/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c316 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-139801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4277641/10000000) (δ := 10609/1000000000) (ψ := -431649/1000000) 212 194
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t316 : ((-4917021309/625000000000 : ℚ) : ℝ) ≤ stT212 316 := by
  have hc : ((-139851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).2
  have h0 : (0:ℝ) ≤ ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4917021309/625000000000 : ℚ) : ℝ)
      = ((35159/625000 : ℚ) : ℝ) * ((-139851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c317 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-362169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 372011/625000) (δ := 10609/1000000000) (ψ := -431649/1000000) 212 194
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t317 : ((-12714277079/312500000000 : ℚ) : ℝ) ≤ stT212 317 := by
  have hc : ((-181097/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).2
  have h0 : (0:ℝ) ≤ ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12714277079/312500000000 : ℚ) : ℝ)
      = ((70207/1250000 : ℚ) : ℝ) * ((-181097/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c318 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-497839/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 952683/1250000) (δ := 10609/1000000000) (ψ := -431649/1000000) 212 194
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t318 : ((-34898586109/625000000000 : ℚ) : ℝ) ≤ stT212 318 := by
  have hc : ((-62233/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34898586109/625000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-62233/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c319 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-420239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1284481/2000000) (δ := 5351/500000000) (ψ := -431649/1000000) 212 195
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t319 : ((-29412858969/625000000000 : ℚ) : ℝ) ≤ stT212 319 := by
  have hc : ((-52533/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29412858969/625000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-52533/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c320 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-328437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4763611/10000000) (δ := 5351/500000000) (ψ := -431649/1000000) 212 195
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t320 : ((-183629817279/10000000000000 : ℚ) : ℝ) ≤ stT212 320 := by
  have hc : ((-328487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183629817279/10000000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-328487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c321 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((321047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -621981/2000000) (δ := 5351/500000000) (ψ := -431649/1000000) 212 195
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t321 : ((35832574113/2000000000000 : ℚ) : ℝ) ≤ stT212 321 := by
  have hc : ((320997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).1
  have hw2 : ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111629/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35832574113/2000000000000 : ℚ) : ℝ)
      = ((111629/2000000 : ℚ) : ℝ) * ((320997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c322 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((833957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1461393/10000000) (δ := 5351/500000000) (ψ := -431649/1000000) 212 195
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t322 : ((232359012573/5000000000000 : ℚ) : ℝ) ≤ stT212 322 := by
  have hc : ((833907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232359012573/5000000000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((833907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c323 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((19947/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 182031/10000000) (δ := 5351/500000000) (ψ := -431649/1000000) 212 195
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t323 : ((2774558411/50000000000 : ℚ) : ℝ) ≤ stT212 323 := by
  have hc : ((9973/10000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2774558411/50000000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((9973/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c324 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((746409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1820367/10000000) (δ := 5351/500000000) (ψ := -431649/1000000) 212 195
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t324 : ((82928694849/2000000000000 : ℚ) : ℝ) ≤ stT212 324 := by
  have hc : ((746359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82928694849/2000000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((746359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c325 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((188221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 690723/2000000) (δ := 5351/500000000) (ψ := -431649/1000000) 212 195
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t325 : ((1043784537/100000000000 : ℚ) : ℝ) ≤ stT212 325 := by
  have hc : ((188171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1043784537/100000000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((188171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c326 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-4457/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5081881/10000000) (δ := 5351/500000000) (ψ := -431649/1000000) 212 195
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t326 : ((-987512767/40000000000 : ℚ) : ℝ) ≤ stT212 326 := by
  have hc : ((-1783/4000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-987512767/40000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-1783/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c327 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-896263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1341033/2000000) (δ := 5351/500000000) (ψ := -431649/1000000) 212 195
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t327 : ((-247831440813/5000000000000 : ℚ) : ℝ) ≤ stT212 327 := by
  have hc : ((-896313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-247831440813/5000000000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-896313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c328 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-196483/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1846111/2500000) (δ := 5397/500000000) (ψ := -431649/1000000) 212 196
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t328 : ((-54247590947/1000000000000 : ℚ) : ℝ) ≤ stT212 328 := by
  have hc : ((-196493/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54247590947/1000000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-196493/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c329 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-672537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5771071/10000000) (δ := 5397/500000000) (ψ := -431649/1000000) 212 196
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t329 : ((-185404659833/5000000000000 : ℚ) : ℝ) ≤ stT212 329 := by
  have hc : ((-672587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185404659833/5000000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-672587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c330 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-47047/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2081287/5000000) (δ := 5397/500000000) (ψ := -431649/1000000) 212 196
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t330 : ((-404879511/78125000000 : ℚ) : ℝ) ≤ stT212 330 := by
  have hc : ((-1471/15625 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).2
  have h0 : (0:ℝ) ≤ ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-404879511/78125000000 : ℚ) : ℝ)
      = ((275241/5000000 : ℚ) : ℝ) * ((-1471/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c331 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((520311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2558953/10000000) (δ := 5397/500000000) (ψ := -431649/1000000) 212 196
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t331 : ((285960938389/10000000000000 : ℚ) : ℝ) ≤ stT212 331 := by
  have hc : ((520261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).1
  have hw2 : ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((549649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((285960938389/10000000000000 : ℚ) : ℝ)
      = ((549649/10000000 : ℚ) : ℝ) * ((520261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c332 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((18543/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -192031/2000000) (δ := 5397/500000000) (ψ := -431649/1000000) 212 196
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t332 : ((5088119491/100000000000 : ℚ) : ℝ) ≤ stT212 332 := by
  have hc : ((9271/10000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).1
  have hw2 : ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5088119491/100000000000 : ℚ) : ℝ)
      = ((548821/10000000 : ℚ) : ℝ) * ((9271/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c333 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((484017/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31691/500000) (δ := 5397/500000000) (ψ := -431649/1000000) 212 196
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t333 : ((8288302501/156250000000 : ℚ) : ℝ) ≤ stT212 333 := by
  have hc : ((60499/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8288302501/156250000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((60499/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c334 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((315013/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 88921/400000) (δ := 5397/500000000) (ψ := -431649/1000000) 212 196
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t334 : ((1723535589/50000000000 : ℚ) : ℝ) ≤ stT212 334 := by
  have hc : ((78747/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1723535589/50000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((78747/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c335 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((47773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3807513/10000000) (δ := 5397/500000000) (ψ := -431649/1000000) 212 196
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t335 : ((13036921417/5000000000000 : ℚ) : ℝ) ≤ stT212 335 := by
  have hc : ((47723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13036921417/5000000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((47723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c336 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-275723/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5387231/10000000) (δ := 5397/500000000) (ψ := -431649/1000000) 212 196
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t336 : ((-7521647133/250000000000 : ℚ) : ℝ) ≤ stT212 336 := by
  have hc : ((-68937/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).2
  have h0 : (0:ℝ) ≤ ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7521647133/250000000000 : ℚ) : ℝ)
      = ((109109/2000000 : ℚ) : ℝ) * ((-68937/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c337 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-468531/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1392457/2000000) (δ := 5397/500000000) (ψ := -431649/1000000) 212 196
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t337 : ((-12761942633/250000000000 : ℚ) : ℝ) ≤ stT212 337 := by
  have hc : ((-117139/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12761942633/250000000000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-117139/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c338 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-963381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7175341/10000000) (δ := 10687/1000000000) (ψ := -431649/1000000) 212 197
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t338 : ((-524038060399/10000000000000 : ℚ) : ℝ) ≤ stT212 338 := by
  have hc : ((-963431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).2
  have h0 : (0:ℝ) ≤ ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-524038060399/10000000000000 : ℚ) : ℝ)
      = ((543929/10000000 : ℚ) : ℝ) * ((-963431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c339 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-623357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2804781/5000000) (δ := 10687/1000000000) (ψ := -431649/1000000) 212 197
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t339 : ((-169294275141/5000000000000 : ℚ) : ℝ) ≤ stT212 339 := by
  have hc : ((-623407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169294275141/5000000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-623407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c340 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-48563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4048447/10000000) (δ := 10687/1000000000) (ψ := -431649/1000000) 212 197
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t340 : ((-26364142451/10000000000000 : ℚ) : ℝ) ≤ stT212 340 := by
  have hc : ((-48613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26364142451/10000000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-48613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c341 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((543011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2491943/10000000) (δ := 10687/1000000000) (ψ := -431649/1000000) 212 197
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t341 : ((29402967033/1000000000000 : ℚ) : ℝ) ≤ stT212 341 := by
  have hc : ((542961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).1
  have hw2 : ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((54153/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29402967033/1000000000000 : ℚ) : ℝ)
      = ((54153/1000000 : ℚ) : ℝ) * ((542961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c342 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((930149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -117493/1250000) (δ := 10687/1000000000) (ψ := -431649/1000000) 212 197
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t342 : ((251469936531/5000000000000 : ℚ) : ℝ) ≤ stT212 342 := by
  have hc : ((930099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).1
  have hw2 : ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((270369/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((251469936531/5000000000000 : ℚ) : ℝ)
      = ((270369/5000000 : ℚ) : ℝ) * ((930099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c343 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((970621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 607497/10000000) (δ := 10687/1000000000) (ψ := -431649/1000000) 212 197
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t343 : ((524058840879/10000000000000 : ℚ) : ℝ) ≤ stT212 343 := by
  have hc : ((970571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((524058840879/10000000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((970571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c344 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((326153/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2150433/10000000) (δ := 10687/1000000000) (ψ := -431649/1000000) 212 197
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t344 : ((10989759429/312500000000 : ℚ) : ℝ) ≤ stT212 344 := by
  have hc : ((20383/31250 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10989759429/312500000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((20383/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c345 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((47543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3688917/10000000) (δ := 10687/1000000000) (ψ := -431649/1000000) 212 197
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t345 : ((12791394179/2500000000000 : ℚ) : ℝ) ≤ stT212 345 := by
  have hc : ((23759/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12791394179/2500000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((23759/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c346 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-247729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 326431/625000) (δ := 10687/1000000000) (ψ := -431649/1000000) 212 197
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t346 : ((-16649192677/625000000000 : ℚ) : ℝ) ≤ stT212 346 := by
  have hc : ((-123877/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).2
  have h0 : (0:ℝ) ≤ ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16649192677/625000000000 : ℚ) : ℝ)
      = ((134401/2500000 : ℚ) : ℝ) * ((-123877/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c347 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-180899/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1688119/2500000) (δ := 10687/1000000000) (ψ := -431649/1000000) 212 197
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t347 : ((-97117197561/2000000000000 : ℚ) : ℝ) ≤ stT212 347 := by
  have hc : ((-180909/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).2
  have h0 : (0:ℝ) ≤ ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97117197561/2000000000000 : ℚ) : ℝ)
      = ((536829/10000000 : ℚ) : ℝ) * ((-180909/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c348 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-492837/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3715153/5000000) (δ := 10623/1000000000) (ψ := -431649/1000000) 212 198
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t348 : ((-132101062567/2500000000000 : ℚ) : ℝ) ≤ stT212 348 := by
  have hc : ((-246431/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).2
  have h0 : (0:ℝ) ≤ ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132101062567/2500000000000 : ℚ) : ℝ)
      = ((536057/10000000 : ℚ) : ℝ) * ((-246431/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c349 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-89057/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5909471/10000000) (δ := 10623/1000000000) (ψ := -431649/1000000) 212 198
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t349 : ((-23837244483/625000000000 : ℚ) : ℝ) ≤ stT212 349 := by
  have hc : ((-356253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).2
  have h0 : (0:ℝ) ≤ ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23837244483/625000000000 : ℚ) : ℝ)
      = ((66911/1250000 : ℚ) : ℝ) * ((-356253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c350 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-9267/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -878607/2000000) (δ := 10623/1000000000) (ψ := -431649/1000000) 212 198
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t350 : ((-9909521897/1000000000000 : ℚ) : ℝ) ≤ stT212 350 := by
  have hc : ((-18539/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9909521897/1000000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-18539/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c351 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((81267/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -720223/2500000) (δ := 10623/1000000000) (ψ := -431649/1000000) 212 198
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t351 : ((33884169/1562500000 : ℚ) : ℝ) ≤ stT212 351 := by
  have hc : ((81257/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).1
  have hw2 : ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((834/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33884169/1562500000 : ℚ) : ℝ)
      = ((834/15625 : ℚ) : ℝ) * ((81257/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c352 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((852923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -274619/2000000) (δ := 10623/1000000000) (ψ := -431649/1000000) 212 198
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t352 : ((454582161873/10000000000000 : ℚ) : ℝ) ≤ stT212 352 := by
  have hc : ((852873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).1
  have hw2 : ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((533001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454582161873/10000000000000 : ℚ) : ℝ)
      = ((533001/10000000 : ℚ) : ℝ) * ((852873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c353 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((998639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65231/5000000) (δ := 10623/1000000000) (ψ := -431649/1000000) 212 198
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t353 : ((265747500447/5000000000000 : ℚ) : ℝ) ≤ stT212 353 := by
  have hc : ((998589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).1
  have hw2 : ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((266123/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265747500447/5000000000000 : ℚ) : ℝ)
      = ((266123/5000000 : ℚ) : ℝ) * ((998589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c354 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((31797/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1629779/10000000) (δ := 10623/1000000000) (ψ := -431649/1000000) 212 198
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t354 : ((1689885173/40000000000 : ℚ) : ℝ) ≤ stT212 354 := by
  have hc : ((6359/8000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1689885173/40000000000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((6359/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c355 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((315397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3124803/10000000) (δ := 10623/1000000000) (ψ := -431649/1000000) 212 198
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t355 : ((20921066021/1250000000000 : ℚ) : ℝ) ≤ stT212 355 := by
  have hc : ((315347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).1
  have hw2 : ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66343/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20921066021/1250000000000 : ℚ) : ℝ)
      = ((66343/1250000 : ℚ) : ℝ) * ((315347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c356 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-27201/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4615693/10000000) (δ := 10623/1000000000) (ψ := -431649/1000000) 212 198
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t356 : ((-7209576397/500000000000 : ℚ) : ℝ) ≤ stT212 356 := by
  have hc : ((-13603/50000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7209576397/500000000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-13603/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c357 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-38221/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6102343/10000000) (δ := 10623/1000000000) (ψ := -431649/1000000) 212 198
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t357 : ((-40460109879/1000000000000 : ℚ) : ℝ) ≤ stT212 357 := by
  have hc : ((-76447/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).2
  have h0 : (0:ℝ) ≤ ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40460109879/1000000000000 : ℚ) : ℝ)
      = ((529257/10000000 : ℚ) : ℝ) * ((-76447/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c358 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-994211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7584859/10000000) (δ := 10623/1000000000) (ψ := -431649/1000000) 212 198
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t358 : ((-525483840937/10000000000000 : ℚ) : ℝ) ≤ stT212 358 := by
  have hc : ((-994261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-525483840937/10000000000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-994261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c359 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-442639/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3322361/5000000) (δ := 1073/100000000) (ψ := -431649/1000000) 212 199
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t359 : ((-1460182537/31250000000 : ℚ) : ℝ) ≤ stT212 359 := by
  have hc : ((-55333/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).2
  have h0 : (0:ℝ) ≤ ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1460182537/31250000000 : ℚ) : ℝ)
      = ((26389/500000 : ℚ) : ℝ) * ((-55333/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c360 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-238559/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5170421/10000000) (δ := 1073/100000000) (ψ := -431649/1000000) 212 199
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t360 : ((-15718122681/625000000000 : ℚ) : ℝ) ≤ stT212 360 := by
  have hc : ((-29823/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).2
  have h0 : (0:ℝ) ≤ ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15718122681/625000000000 : ℚ) : ℝ)
      = ((527047/10000000 : ℚ) : ℝ) * ((-29823/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c361 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((9057/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1850127/5000000) (δ := 1073/100000000) (ψ := -431649/1000000) 212 199
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t361 : ((238210169/50000000000 : ℚ) : ℝ) ≤ stT212 361 := by
  have hc : ((2263/25000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238210169/50000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((2263/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c362 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((25063/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -446823/2000000) (δ := 1073/100000000) (ψ := -431649/1000000) 212 199
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t362 : ((3292940217/100000000000 : ℚ) : ℝ) ≤ stT212 362 := by
  have hc : ((25061/40000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3292940217/100000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((25061/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c363 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((238173/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -772057/10000000) (δ := 1073/100000000) (ψ := -431649/1000000) 212 199
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t363 : ((250003269023/5000000000000 : ℚ) : ℝ) ≤ stT212 363 := by
  have hc : ((476321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).1
  have hw2 : ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((524863/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250003269023/5000000000000 : ℚ) : ℝ)
      = ((524863/10000000 : ℚ) : ℝ) * ((476321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c364 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((962591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 685973/10000000) (δ := 1073/100000000) (ψ := -431649/1000000) 212 199
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t364 : ((252254082411/5000000000000 : ℚ) : ℝ) ≤ stT212 364 := by
  have hc : ((962541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).1
  have hw2 : ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252254082411/5000000000000 : ℚ) : ℝ)
      = ((262071/5000000 : ℚ) : ℝ) * ((962541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c365 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((131091/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 535007/2500000) (δ := 1073/100000000) (ψ := -431649/1000000) 212 199
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t365 : ((68610810263/2000000000000 : ℚ) : ℝ) ≤ stT212 365 := by
  have hc : ((131081/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).1
  have hw2 : ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((523423/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68610810263/2000000000000 : ℚ) : ℝ)
      = ((523423/10000000 : ℚ) : ℝ) * ((131081/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c366 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((67173/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 897527/2500000) (δ := 1073/100000000) (ψ := -431649/1000000) 212 199
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t366 : ((2193674799/312500000000 : ℚ) : ℝ) ≤ stT212 366 := by
  have hc : ((16787/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).1
  have hw2 : ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((130677/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2193674799/312500000000 : ℚ) : ℝ)
      = ((130677/2500000 : ℚ) : ℝ) * ((16787/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c367 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-214637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5036213/10000000) (δ := 1073/100000000) (ψ := -431649/1000000) 212 199
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t367 : ((-14006588169/625000000000 : ℚ) : ℝ) ≤ stT212 367 := by
  have hc : ((-107331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14006588169/625000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-107331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c368 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-426201/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1619599/2500000) (δ := 1073/100000000) (ψ := -431649/1000000) 212 199
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t368 : ((-111093036431/2500000000000 : ℚ) : ℝ) ≤ stT212 368 := by
  have hc : ((-213113/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).2
  have h0 : (0:ℝ) ≤ ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111093036431/2500000000000 : ℚ) : ℝ)
      = ((521287/10000000 : ℚ) : ℝ) * ((-213113/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c369 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-499843/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7791307/10000000) (δ := 5383/500000000) (ψ := -431649/1000000) 212 200
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t369 : ((-3252766043/62500000000 : ℚ) : ℝ) ≤ stT212 369 := by
  have hc : ((-124967/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).2
  have h0 : (0:ℝ) ≤ ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3252766043/62500000000 : ℚ) : ℝ)
      = ((26029/500000 : ℚ) : ℝ) * ((-124967/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c370 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-412999/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1271383/2000000) (δ := 5383/500000000) (ψ := -431649/1000000) 212 200
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t370 : ((-1677509883/39062500000 : ℚ) : ℝ) ≤ stT212 370 := by
  have hc : ((-12907/15625 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1677509883/39062500000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-12907/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c371 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-389217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -985289/2000000) (δ := 5383/500000000) (ψ := -431649/1000000) 212 200
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t371 : ((-8083907789/400000000000 : ℚ) : ℝ) ≤ stT212 371 := by
  have hc : ((-389267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8083907789/400000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-389267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c372 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((3401/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3499791/10000000) (δ := 5383/500000000) (ψ := -431649/1000000) 212 200
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t372 : ((352563/40000000 : ℚ) : ℝ) ≤ stT212 372 := by
  have hc : ((17/100 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).1
  have hw2 : ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((20739/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352563/40000000 : ℚ) : ℝ)
      = ((20739/400000 : ℚ) : ℝ) * ((17/100 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c373 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((674299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2076953/10000000) (δ := 5383/500000000) (ψ := -431649/1000000) 212 200
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t373 : ((17455632361/500000000000 : ℚ) : ℝ) ≤ stT212 373 := by
  have hc : ((674249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).1
  have hw2 : ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25889/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17455632361/500000000000 : ℚ) : ℝ)
      = ((25889/500000 : ℚ) : ℝ) * ((674249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c374 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((241391/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10281/156250) (δ := 5383/500000000) (ψ := -431649/1000000) 212 200
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t374 : ((249627368859/5000000000000 : ℚ) : ℝ) ≤ stT212 374 := by
  have hc : ((482757/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).1
  have hw2 : ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((517087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249627368859/5000000000000 : ℚ) : ℝ)
      = ((517087/10000000 : ℚ) : ℝ) * ((482757/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c375 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((119309/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30291/400000) (δ := 5383/500000000) (ψ := -431649/1000000) 212 200
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t375 : ((246430328767/5000000000000 : ℚ) : ℝ) ≤ stT212 375 := by
  have hc : ((477211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((246430328767/5000000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((477211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c376 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((129349/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1084359/5000000) (δ := 5383/500000000) (ψ := -431649/1000000) 212 200
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t376 : ((6670141569/200000000000 : ℚ) : ℝ) ≤ stT212 376 := by
  have hc : ((129339/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6670141569/200000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((129339/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c377 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((69889/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1788199/5000000) (δ := 5383/500000000) (ψ := -431649/1000000) 212 200
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t377 : ((2248861029/312500000000 : ℚ) : ℝ) ≤ stT212 377 := by
  have hc : ((8733/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2248861029/312500000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((8733/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c378 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-204497/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 311273/625000) (δ := 5383/500000000) (ψ := -431649/1000000) 212 200
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t378 : ((-10519486809/500000000000 : ℚ) : ℝ) ≤ stT212 378 := by
  have hc : ((-102261/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).2
  have h0 : (0:ℝ) ≤ ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10519486809/500000000000 : ℚ) : ℝ)
      = ((102869/2000000 : ℚ) : ℝ) * ((-102261/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c379 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-831319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6380681/10000000) (δ := 5383/500000000) (ψ := -431649/1000000) 212 200
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t379 : ((-213522994377/5000000000000 : ℚ) : ℝ) ≤ stT212 379 := by
  have hc : ((-831369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213522994377/5000000000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-831369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c380 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-999529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7777231/10000000) (δ := 5383/500000000) (ψ := -431649/1000000) 212 200
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t380 : ((-51277403121/1000000000000 : ℚ) : ℝ) ≤ stT212 380 := by
  have hc : ((-999579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51277403121/1000000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-999579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c381 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-864593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6537839/10000000) (δ := 5329/500000000) (ψ := -431649/1000000) 212 201
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t381 : ((-110742610797/2500000000000 : ℚ) : ℝ) ≤ stT212 381 := by
  have hc : ((-864643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110742610797/2500000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-864643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c382 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-469411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -102971/200000) (δ := 5329/500000000) (ψ := -431649/1000000) 212 201
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t382 : ((-48039474669/2000000000000 : ℚ) : ℝ) ≤ stT212 382 := by
  have hc : ((-469461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).2
  have h0 : (0:ℝ) ≤ ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48039474669/2000000000000 : ℚ) : ℝ)
      = ((102329/2000000 : ℚ) : ℝ) * ((-469461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c383 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((65561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3762971/10000000) (δ := 5329/500000000) (ψ := -431649/1000000) 212 201
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t383 : ((32689989/9765625000 : ℚ) : ℝ) ≤ stT212 383 := by
  have hc : ((65511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32689989/9765625000 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((65511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c384 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((144937/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2380943/10000000) (δ := 5329/500000000) (ψ := -431649/1000000) 212 201
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t384 : ((14791284319/500000000000 : ℚ) : ℝ) ≤ stT212 384 := by
  have hc : ((289849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14791284319/500000000000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((289849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c385 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((230167/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1002519/10000000) (δ := 5329/500000000) (ψ := -431649/1000000) 212 201
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t385 : ((234595100923/5000000000000 : ℚ) : ℝ) ≤ stT212 385 := by
  have hc : ((460309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234595100923/5000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((460309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c386 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((247233/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 372301/10000000) (δ := 5329/500000000) (ψ := -431649/1000000) 212 201
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t386 : ((125831773413/2500000000000 : ℚ) : ℝ) ≤ stT212 386 := by
  have hc : ((494441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).1
  have hw2 : ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((254493/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125831773413/2500000000000 : ℚ) : ℝ)
      = ((254493/5000000 : ℚ) : ℝ) * ((494441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c387 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((766497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 174357/1000000) (δ := 5329/500000000) (ψ := -431649/1000000) 212 201
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t387 : ((48700808827/1250000000000 : ℚ) : ℝ) ≤ stT212 387 := by
  have hc : ((766447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).1
  have hw2 : ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((63541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48700808827/1250000000000 : ℚ) : ℝ)
      = ((63541/1250000 : ℚ) : ℝ) * ((766447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c388 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((320503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3111341/10000000) (δ := 5329/500000000) (ψ := -431649/1000000) 212 201
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t388 : ((162685335869/10000000000000 : ℚ) : ℝ) ≤ stT212 388 := by
  have hc : ((320453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).1
  have hw2 : ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162685335869/10000000000000 : ℚ) : ℝ)
      = ((507673/10000000 : ℚ) : ℝ) * ((320453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c389 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-217671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4475561/10000000) (δ := 5329/500000000) (ψ := -431649/1000000) 212 201
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t389 : ((-110389119141/10000000000000 : ℚ) : ℝ) ≤ stT212 389 := by
  have hc : ((-217721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110389119141/10000000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-217721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c390 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-691611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5836283/10000000) (δ := 5329/500000000) (ψ := -431649/1000000) 212 201
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t390 : ((-35023638057/1000000000000 : ℚ) : ℝ) ≤ stT212 390 := by
  have hc : ((-691661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).2
  have h0 : (0:ℝ) ≤ ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35023638057/1000000000000 : ℚ) : ℝ)
      = ((50637/1000000 : ℚ) : ℝ) * ((-691661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c391 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-120663/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7193507/10000000) (δ := 5329/500000000) (ψ := -431649/1000000) 212 201
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t391 : ((-122050188897/2500000000000 : ℚ) : ℝ) ≤ stT212 391 := by
  have hc : ((-482677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).2
  have h0 : (0:ℝ) ≤ ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122050188897/2500000000000 : ℚ) : ℝ)
      = ((252861/5000000 : ℚ) : ℝ) * ((-482677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c392 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-15028/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7160677/10000000) (δ := 2663/250000000) (ψ := -431649/1000000) 212 202
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t392 : ((-242902135917/5000000000000 : ℚ) : ℝ) ≤ stT212 392 := by
  have hc : ((-480921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).2
  have h0 : (0:ℝ) ≤ ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242902135917/5000000000000 : ℚ) : ℝ)
      = ((505077/10000000 : ℚ) : ℝ) * ((-480921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c393 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-684079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5810343/10000000) (δ := 2663/250000000) (ψ := -431649/1000000) 212 202
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t393 : ((-172548963993/5000000000000 : ℚ) : ℝ) ≤ stT212 393 := by
  have hc : ((-684129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).2
  have h0 : (0:ℝ) ≤ ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172548963993/5000000000000 : ℚ) : ℝ)
      = ((252217/5000000 : ℚ) : ℝ) * ((-684129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c394 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-106471/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2231727/5000000) (δ := 2663/250000000) (ψ := -431649/1000000) 212 202
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t394 : ((-13098618/1220703125 : ℚ) : ℝ) ≤ stT212 394 := by
  have hc : ((-3328/15625 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).2
  have h0 : (0:ℝ) ≤ ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13098618/1220703125 : ℚ) : ℝ)
      = ((503793/10000000 : ℚ) : ℝ) * ((-3328/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c395 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((9913/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -312001/1000000) (δ := 2663/250000000) (ψ := -431649/1000000) 212 202
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t395 : ((39895835391/2500000000000 : ℚ) : ℝ) ≤ stT212 395 := by
  have hc : ((158583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).1
  have hw2 : ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39895835391/2500000000000 : ℚ) : ℝ)
      = ((251577/5000000 : ℚ) : ℝ) * ((158583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c396 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((378541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -355981/2000000) (δ := 2663/250000000) (ψ := -431649/1000000) 212 202
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t396 : ((23776387911/625000000000 : ℚ) : ℝ) ≤ stT212 396 := by
  have hc : ((94629/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).1
  have hw2 : ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251259/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23776387911/625000000000 : ℚ) : ℝ)
      = ((251259/5000000 : ℚ) : ℝ) * ((94629/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c397 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((246081/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -88649/2000000) (δ := 2663/250000000) (ψ := -431649/1000000) 212 202
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t397 : ((49399235649/1000000000000 : ℚ) : ℝ) ≤ stT212 397 := by
  have hc : ((492137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).1
  have hw2 : ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((100377/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49399235649/1000000000000 : ℚ) : ℝ)
      = ((100377/2000000 : ℚ) : ℝ) * ((492137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c398 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((2929/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 890129/10000000) (δ := 2663/250000000) (ψ := -431649/1000000) 212 202
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t398 : ((23489514321/500000000000 : ℚ) : ℝ) ≤ stT212 398 := by
  have hc : ((93723/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).1
  have hw2 : ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250627/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23489514321/500000000000 : ℚ) : ℝ)
      = ((250627/5000000 : ℚ) : ℝ) * ((93723/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c399 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((63093/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2220111/10000000) (δ := 2663/250000000) (ψ := -431649/1000000) 212 202
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t399 : ((986984159/31250000000 : ℚ) : ℝ) ≤ stT212 399 := by
  have hc : ((3943/6250 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).1
  have hw2 : ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((986984159/31250000000 : ℚ) : ℝ)
      = ((250313/5000000 : ℚ) : ℝ) * ((3943/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c400 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((151509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1773377/5000000) (δ := 2663/250000000) (ψ := -431649/1000000) 212 202
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t400 : ((151459/20000000 : ℚ) : ℝ) ≤ stT212 400 := by
  have hc : ((151459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).1
  have hw2 : ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/20 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151459/20000000 : ℚ) : ℝ)
      = ((1/20 : ℚ) : ℝ) * ((151459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c401 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-368363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4870111/10000000) (δ := 2663/250000000) (ψ := -431649/1000000) 212 202
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t401 : ((-183976978701/10000000000000 : ℚ) : ℝ) ≤ stT212 401 := by
  have hc : ((-368413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183976978701/10000000000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-368413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c402 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-786583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6190129/10000000) (δ := 2663/250000000) (ψ := -431649/1000000) 212 202
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t402 : ((-78467428383/2000000000000 : ℚ) : ℝ) ≤ stT212 402 := by
  have hc : ((-786633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78467428383/2000000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-786633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c403 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-990379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3753457/5000000) (δ := 2663/250000000) (ψ := -431649/1000000) 212 202
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t403 : ((-61671042543/1250000000000 : ℚ) : ℝ) ≤ stT212 403 := by
  have hc : ((-990429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61671042543/1250000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-990429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c404 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-926207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137751/200000) (δ := 10759/1000000000) (ψ := -431649/1000000) 212 203
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t404 : ((-460830456383/10000000000000 : ℚ) : ℝ) ≤ stT212 404 := by
  have hc : ((-926257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-460830456383/10000000000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-926257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c405 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-613209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1394321/2500000) (δ := 10759/1000000000) (ψ := -431649/1000000) 212 203
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t405 : ((-38091356267/1250000000000 : ℚ) : ℝ) ≤ stT212 405 := by
  have hc : ((-613259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).2
  have h0 : (0:ℝ) ≤ ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38091356267/1250000000000 : ℚ) : ℝ)
      = ((62113/1250000 : ℚ) : ℝ) * ((-613259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c406 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-136873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4270251/10000000) (δ := 10759/1000000000) (ψ := -431649/1000000) 212 203
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t406 : ((-16988447379/2500000000000 : ℚ) : ℝ) ≤ stT212 406 := by
  have hc : ((-136923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).2
  have h0 : (0:ℝ) ≤ ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16988447379/2500000000000 : ℚ) : ℝ)
      = ((124073/2500000 : ℚ) : ℝ) * ((-136923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c407 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((23427/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2966451/10000000) (δ := 10759/1000000000) (ψ := -431649/1000000) 212 203
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t407 : ((92886158271/5000000000000 : ℚ) : ℝ) ≤ stT212 407 := by
  have hc : ((187391/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92886158271/5000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((187391/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c408 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((393047/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1665831/10000000) (δ := 10759/1000000000) (ψ := -431649/1000000) 212 203
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t408 : ((97287290303/2500000000000 : ℚ) : ℝ) ≤ stT212 408 := by
  have hc : ((196511/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97287290303/2500000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((196511/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c409 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((989163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -368391/10000000) (δ := 10759/1000000000) (ψ := -431649/1000000) 212 203
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t409 : ((122271181721/2500000000000 : ℚ) : ℝ) ≤ stT212 409 := by
  have hc : ((989113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122271181721/2500000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((989113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c410 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((466101/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 925869/10000000) (δ := 10759/1000000000) (ψ := -431649/1000000) 212 203
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t410 : ((7193067427/156250000000 : ℚ) : ℝ) ≤ stT212 410 := by
  have hc : ((116519/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7193067427/156250000000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((116519/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c411 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((126379/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1108501/5000000) (δ := 10759/1000000000) (ψ := -431649/1000000) 212 203
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t411 : ((62333152047/2000000000000 : ℚ) : ℝ) ≤ stT212 411 := by
  have hc : ((126369/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).1
  have hw2 : ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((493263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62333152047/2000000000000 : ℚ) : ℝ)
      = ((493263/10000000 : ℚ) : ℝ) * ((126369/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c412 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((84007/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 700991/2000000) (δ := 10759/1000000000) (ψ := -431649/1000000) 212 203
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t412 : ((2585931753/312500000000 : ℚ) : ℝ) ≤ stT212 412 := by
  have hc : ((41991/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2585931753/312500000000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((41991/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c413 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-169153/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4789781/10000000) (δ := 10759/1000000000) (ψ := -431649/1000000) 212 203
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t413 : ((-10405885013/625000000000 : ℚ) : ℝ) ≤ stT212 413 := by
  have hc : ((-84589/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10405885013/625000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-84589/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c414 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-11819/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6071533/10000000) (δ := 10759/1000000000) (ψ := -431649/1000000) 212 203
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t414 : ((-92945842721/2500000000000 : ℚ) : ℝ) ≤ stT212 414 := by
  have hc : ((-378233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92945842721/2500000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-378233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c415 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-489883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7350211/10000000) (δ := 10759/1000000000) (ψ := -431649/1000000) 212 203
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t415 : ((-60121632237/1250000000000 : ℚ) : ℝ) ≤ stT212 415 := by
  have hc : ((-122477/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60121632237/1250000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-122477/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c416 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-476363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3541101/5000000) (δ := 10737/1000000000) (ψ := -431649/1000000) 212 204
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t416 : ((-58392187227/1250000000000 : ℚ) : ℝ) ≤ stT212 416 := by
  have hc : ((-119097/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58392187227/1250000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-119097/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c417 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-170971/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -726209/1250000) (δ := 10737/1000000000) (ψ := -431649/1000000) 212 204
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t417 : ((-167462265801/5000000000000 : ℚ) : ℝ) ≤ stT212 417 := by
  have hc : ((-341967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167462265801/5000000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-341967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c418 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-121419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -567527/1250000) (δ := 10737/1000000000) (ψ := -431649/1000000) 212 204
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t418 : ((-3712512719/312500000000 : ℚ) : ℝ) ≤ stT212 418 := by
  have hc : ((-30361/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).2
  have h0 : (0:ℝ) ≤ ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3712512719/312500000000 : ℚ) : ℝ)
      = ((122279/2500000 : ℚ) : ℝ) * ((-30361/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c419 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((258321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3273781/10000000) (δ := 10737/1000000000) (ψ := -431649/1000000) 212 204
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t419 : ((126173389901/10000000000000 : ℚ) : ℝ) ≤ stT212 419 := by
  have hc : ((258271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126173389901/10000000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((258271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c420 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((346863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2010367/10000000) (δ := 10737/1000000000) (ψ := -431649/1000000) 212 204
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t420 : ((1692396021/50000000000 : ℚ) : ℝ) ≤ stT212 420 := by
  have hc : ((173419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1692396021/50000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((173419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c421 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((47767/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -374987/5000000) (δ := 10737/1000000000) (ψ := -431649/1000000) 212 204
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t421 : ((4655796873/100000000000 : ℚ) : ℝ) ≤ stT212 421 := by
  have hc : ((95529/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4655796873/100000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((95529/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c422 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((97947/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 507451/10000000) (δ := 10737/1000000000) (ψ := -431649/1000000) 212 204
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t422 : ((2979836379/62500000000 : ℚ) : ℝ) ≤ stT212 422 := by
  have hc : ((48971/50000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2979836379/62500000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((48971/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c423 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((761779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 352371/2000000) (δ := 10737/1000000000) (ψ := -431649/1000000) 212 204
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t423 : ((46295603433/1250000000000 : ℚ) : ℝ) ≤ stT212 423 := by
  have hc : ((761729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46295603433/1250000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((761729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c424 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((178689/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94167/312500) (δ := 10737/1000000000) (ψ := -431649/1000000) 212 204
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t424 : ((5422921393/312500000000 : ℚ) : ℝ) ≤ stT212 424 := by
  have hc : ((22333/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5422921393/312500000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((22333/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c425 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-133549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 852373/2000000) (δ := 10737/1000000000) (ψ := -431649/1000000) 212 204
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t425 : ((-4050320883/625000000000 : ℚ) : ℝ) ≤ stT212 425 := by
  have hc : ((-133599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4050320883/625000000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-133599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c426 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-118183/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5507471/10000000) (δ := 10737/1000000000) (ψ := -431649/1000000) 212 204
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t426 : ((-28632372443/1000000000000 : ℚ) : ℝ) ≤ stT212 426 := by
  have hc : ((-118193/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28632372443/1000000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-118193/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c427 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-9041/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3375081/5000000) (δ := 10737/1000000000) (ψ := -431649/1000000) 212 204
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t427 : ((-4375489261/100000000000 : ℚ) : ℝ) ≤ stT212 427 := by
  have hc : ((-18083/20000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4375489261/100000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-18083/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c428 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-998523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3859039/5000000) (δ := 1063/100000000) (ψ := -431649/1000000) 212 205
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t428 : ((-482679232437/10000000000000 : ℚ) : ℝ) ≤ stT212 428 := by
  have hc : ((-998573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-482679232437/10000000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-998573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c429 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-42649/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1620291/2500000) (δ := 1063/100000000) (ψ := -431649/1000000) 212 205
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t429 : ((-8236942983/200000000000 : ℚ) : ℝ) ≤ stT212 429 := by
  have hc : ((-85303/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8236942983/200000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-85303/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c430 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-503867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1049433/2000000) (δ := 1063/100000000) (ψ := -431649/1000000) 212 205
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t430 : ((-243010445831/10000000000000 : ℚ) : ℝ) ≤ stT212 430 := by
  have hc : ((-503917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243010445831/10000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-503917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c431 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-35629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4016081/10000000) (δ := 1063/100000000) (ψ := -431649/1000000) 212 205
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t431 : ((-4296500859/2500000000000 : ℚ) : ℝ) ≤ stT212 431 := by
  have hc : ((-35679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).2
  have h0 : (0:ℝ) ≤ ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4296500859/2500000000000 : ℚ) : ℝ)
      = ((120421/2500000 : ℚ) : ℝ) * ((-35679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c432 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((110017/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1393903/5000000) (δ := 1063/100000000) (ψ := -431649/1000000) 212 205
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t432 : ((846814641/40000000000 : ℚ) : ℝ) ≤ stT212 432 := by
  have hc : ((220009/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((846814641/40000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((220009/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c433 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((811001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -78117/500000) (δ := 1063/100000000) (ψ := -431649/1000000) 212 205
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t433 : ((389717911119/10000000000000 : ℚ) : ℝ) ≤ stT212 433 := by
  have hc : ((810951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((389717911119/10000000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((810951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c434 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((990781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42467/1250000) (δ := 1063/100000000) (ψ := -431649/1000000) 212 205
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t434 : ((95113148193/2000000000000 : ℚ) : ℝ) ≤ stT212 434 := by
  have hc : ((990731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95113148193/2000000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((990731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c435 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((938677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 880059/10000000) (δ := 1063/100000000) (ψ := -431649/1000000) 212 205
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t435 : ((450036917301/10000000000000 : ℚ) : ℝ) ≤ stT212 435 := by
  have hc : ((938627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((450036917301/10000000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((938627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c436 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((668343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 419409/2000000) (δ := 1063/100000000) (ψ := -431649/1000000) 212 205
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t436 : ((320054205509/10000000000000 : ℚ) : ℝ) ≤ stT212 436 := by
  have hc : ((668293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320054205509/10000000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((668293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c437 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((9753/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1655611/5000000) (δ := 1063/100000000) (ψ := -431649/1000000) 212 205
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t437 : ((1166131841/100000000000 : ℚ) : ℝ) ≤ stT212 437 := by
  have hc : ((9751/40000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).1
  have hw2 : ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((119591/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1166131841/100000000000 : ℚ) : ℝ)
      = ((119591/2500000 : ℚ) : ℝ) * ((9751/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c438 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-118017/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 565337/1250000) (δ := 1063/100000000) (ψ := -431649/1000000) 212 205
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t438 : ((-28201355199/2500000000000 : ℚ) : ℝ) ≤ stT212 438 := by
  have hc : ((-59021/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28201355199/2500000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-59021/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c439 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-330349/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5731361/10000000) (δ := 1063/100000000) (ψ := -431649/1000000) 212 205
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t439 : ((-39419730119/1250000000000 : ℚ) : ℝ) ≤ stT212 439 := by
  have hc : ((-165187/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39419730119/1250000000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-165187/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c440 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-933521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 693727/1000000) (δ := 1063/100000000) (ψ := -431649/1000000) 212 205
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t440 : ((-111265792493/2500000000000 : ℚ) : ℝ) ≤ stT212 440 := by
  have hc : ((-933571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111265792493/2500000000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-933571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c441 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-993443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -378377/500000) (δ := 267/25000000) (ψ := -431649/1000000) 212 206
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t441 : ((-473092425163/10000000000000 : ℚ) : ℝ) ≤ stT212 441 := by
  have hc : ((-993493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-473092425163/10000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-993493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c442 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-165657/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -636709/1000000) (δ := 267/25000000) (ψ := -431649/1000000) 212 206
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t442 : ((-19699959971/500000000000 : ℚ) : ℝ) ≤ stT212 442 := by
  have hc : ((-165667/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19699959971/500000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-165667/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c443 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-476739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5169343/10000000) (δ := 267/25000000) (ψ := -431649/1000000) 212 206
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t443 : ((-45305921147/2000000000000 : ℚ) : ℝ) ≤ stT212 443 := by
  have hc : ((-476789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45305921147/2000000000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-476789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c444 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-9461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3974299/10000000) (δ := 267/25000000) (ψ := -431649/1000000) 212 206
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t444 : ((-2250928197/2500000000000 : ℚ) : ℝ) ≤ stT212 444 := by
  have hc : ((-4743/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2250928197/2500000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-4743/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c445 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((442167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1390979/5000000) (δ := 267/25000000) (ψ := -431649/1000000) 212 206
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t445 : ((41916670653/2000000000000 : ℚ) : ℝ) ≤ stT212 445 := by
  have hc : ((442117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41916670653/2000000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((442117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c446 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((803939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1592267/10000000) (δ := 267/25000000) (ψ := -431649/1000000) 212 206
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t446 : ((380651892057/10000000000000 : ℚ) : ℝ) ≤ stT212 446 := by
  have hc : ((803889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((380651892057/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((803889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c447 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((986889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -405279/10000000) (δ := 267/25000000) (ψ := -431649/1000000) 212 206
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t447 : ((466758070737/10000000000000 : ℚ) : ℝ) ≤ stT212 447 := by
  have hc : ((986839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((466758070737/10000000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((986839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c448 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((951831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97389/1250000) (δ := 267/25000000) (ψ := -431649/1000000) 212 206
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t448 : ((89934738471/2000000000000 : ℚ) : ℝ) ≤ stT212 448 := by
  have hc : ((951781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89934738471/2000000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((951781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c449 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((707869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2451/12500) (δ := 267/25000000) (ψ := -431649/1000000) 212 206
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t449 : ((334040312851/10000000000000 : ℚ) : ℝ) ≤ stT212 449 := by
  have hc : ((707819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334040312851/10000000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((707819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c450 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((9677/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3139891/10000000) (δ := 267/25000000) (ψ := -431649/1000000) 212 206
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t450 : ((18244159757/1250000000000 : ℚ) : ℝ) ≤ stT212 450 := by
  have hc : ((154807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18244159757/1250000000000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((154807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c451 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-155129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 863277/2000000) (δ := 267/25000000) (ψ := -431649/1000000) 212 206
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t451 : ((-36535498939/5000000000000 : ℚ) : ℝ) ≤ stT212 451 := by
  have hc : ((-155179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36535498939/5000000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-155179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c452 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-585337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5490229/10000000) (δ := 267/25000000) (ψ := -431649/1000000) 212 206
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t452 : ((-275343214707/10000000000000 : ℚ) : ℝ) ≤ stT212 452 := by
  have hc : ((-585387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275343214707/10000000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-585387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c453 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-177677/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6661529/10000000) (δ := 267/25000000) (ψ := -431649/1000000) 212 206
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t453 : ((-83484637767/2000000000000 : ℚ) : ℝ) ≤ stT212 453 := by
  have hc : ((-177687/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83484637767/2000000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-177687/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c454 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-199991/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7830179/10000000) (δ := 267/25000000) (ψ := -431649/1000000) 212 206
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t454 : ((-23466317331/500000000000 : ℚ) : ℝ) ≤ stT212 454 := by
  have hc : ((-200001/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23466317331/500000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-200001/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c455 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-448703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53693/80000) (δ := 2697/250000000) (ψ := -431649/1000000) 212 207
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t455 : ((-3286988691/78125000000 : ℚ) : ℝ) ≤ stT212 455 := by
  have hc : ((-56091/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3286988691/78125000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-56091/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c456 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-120787/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5548063/10000000) (δ := 2697/250000000) (ψ := -431649/1000000) 212 207
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t456 : ((-56568389521/2000000000000 : ℚ) : ℝ) ≤ stT212 456 := by
  have hc : ((-120797/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56568389521/2000000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-120797/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c457 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-91503/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2193549/5000000) (δ := 2697/250000000) (ψ := -431649/1000000) 212 207
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t457 : ((-5351882421/625000000000 : ℚ) : ℝ) ≤ stT212 457 := by
  have hc : ((-11441/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).2
  have h0 : (0:ℝ) ≤ ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5351882421/625000000000 : ℚ) : ℝ)
      = ((467781/10000000 : ℚ) : ℝ) * ((-11441/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c458 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((17233/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -201789/625000) (δ := 2697/250000000) (ψ := -431649/1000000) 212 207
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t458 : ((64407891691/5000000000000 : ℚ) : ℝ) ≤ stT212 458 := by
  have hc : ((137839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64407891691/5000000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((137839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c459 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((168893/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2072641/10000000) (δ := 2697/250000000) (ψ := -431649/1000000) 212 207
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t459 : ((3941333109/125000000000 : ℚ) : ℝ) ≤ stT212 459 := by
  have hc : ((337761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3941333109/125000000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((337761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c460 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((233289/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -183851/2000000) (δ := 2697/250000000) (ψ := -431649/1000000) 212 207
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t460 : ((54382817339/1250000000000 : ℚ) : ℝ) ≤ stT212 460 := by
  have hc : ((466553/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54382817339/1250000000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((466553/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c461 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((995709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 231693/10000000) (δ := 2697/250000000) (ψ := -431649/1000000) 212 207
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t461 : ((231862098307/5000000000000 : ℚ) : ℝ) ≤ stT212 461 := by
  have hc : ((995659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231862098307/5000000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((995659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c462 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((851457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1380097/10000000) (δ := 2697/250000000) (ψ := -431649/1000000) 212 207
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t462 : ((198055147747/5000000000000 : ℚ) : ℝ) ≤ stT212 462 := by
  have hc : ((851407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198055147747/5000000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((851407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c463 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((531501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2526063/10000000) (δ := 2697/250000000) (ψ := -431649/1000000) 212 207
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t463 : ((246986006289/10000000000000 : ℚ) : ℝ) ≤ stT212 463 := by
  have hc : ((531451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((246986006289/10000000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((531451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c464 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((102799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1834769/5000000) (δ := 2697/250000000) (ψ := -431649/1000000) 212 207
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t464 : ((23849995131/5000000000000 : ℚ) : ℝ) ≤ stT212 464 := by
  have hc : ((102749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23849995131/5000000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((102749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c465 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-346121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 192423/400000) (δ := 2697/250000000) (ψ := -431649/1000000) 212 207
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t465 : ((-160532993369/10000000000000 : ℚ) : ℝ) ≤ stT212 465 := by
  have hc : ((-346171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).2
  have h0 : (0:ℝ) ≤ ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160532993369/10000000000000 : ℚ) : ℝ)
      = ((463739/10000000 : ℚ) : ℝ) * ((-346171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c466 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-144699/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5949121/10000000) (δ := 2697/250000000) (ψ := -431649/1000000) 212 207
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t466 : ((-33517643289/1000000000000 : ℚ) : ℝ) ≤ stT212 466 := by
  have hc : ((-144709/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).2
  have h0 : (0:ℝ) ≤ ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33517643289/1000000000000 : ℚ) : ℝ)
      = ((231621/5000000 : ℚ) : ℝ) * ((-144709/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c467 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-953093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7085229/10000000) (δ := 2697/250000000) (ψ := -431649/1000000) 212 207
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t467 : ((-88212431507/2000000000000 : ℚ) : ℝ) ≤ stT212 467 := by
  have hc : ((-953143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88212431507/2000000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-953143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c468 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-494683/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1497813/2000000) (δ := 2677/250000000) (ψ := -431649/1000000) 212 208
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t468 : ((-57169816927/1250000000000 : ℚ) : ℝ) ≤ stT212 468 := by
  have hc : ((-123677/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57169816927/1250000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-123677/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c469 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-826193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -317889/500000) (δ := 2677/250000000) (ψ := -431649/1000000) 212 208
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t469 : ((-190762157597/5000000000000 : ℚ) : ℝ) ≤ stT212 469 := by
  have hc : ((-826243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190762157597/5000000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-826243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c470 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-248777/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5228933/10000000) (δ := 2677/250000000) (ψ := -431649/1000000) 212 208
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t470 : ((-28690975833/1250000000000 : ℚ) : ℝ) ≤ stT212 470 := by
  have hc : ((-124401/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28690975833/1250000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-124401/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c471 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-35067/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4102471/10000000) (δ := 2677/250000000) (ψ := -431649/1000000) 212 208
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t471 : ((-505298481/156250000000 : ℚ) : ℝ) ≤ stT212 471 := by
  have hc : ((-8773/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-505298481/156250000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-8773/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c472 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((370399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1489197/5000000) (δ := 2677/250000000) (ψ := -431649/1000000) 212 208
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t472 : ((170466830163/10000000000000 : ℚ) : ℝ) ≤ stT212 472 := by
  have hc : ((370349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170466830163/10000000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((370349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c473 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((368329/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -928351/5000000) (δ := 2677/250000000) (ψ := -431649/1000000) 212 208
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t473 : ((52920681/1562500000 : ℚ) : ℝ) ≤ stT212 473 := by
  have hc : ((23019/31250 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52920681/1562500000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((23019/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c474 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((956821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -368671/5000000) (δ := 2677/250000000) (ψ := -431649/1000000) 212 208
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t474 : ((87891854373/2000000000000 : ℚ) : ℝ) ≤ stT212 474 := by
  have hc : ((956771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87891854373/2000000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((956771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c475 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((247123/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 379633/10000000) (δ := 2677/250000000) (ψ := -431649/1000000) 212 208
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t475 : ((226763915651/5000000000000 : ℚ) : ℝ) ≤ stT212 475 := by
  have hc : ((494221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226763915651/5000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((494221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c476 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((413319/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1494223/10000000) (δ := 2677/250000000) (ψ := -431649/1000000) 212 208
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t476 : ((94716445803/2500000000000 : ℚ) : ℝ) ≤ stT212 476 := by
  have hc : ((206647/250000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94716445803/2500000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((206647/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c477 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((503983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2606481/10000000) (δ := 2677/250000000) (ψ := -431649/1000000) 212 208
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t477 : ((57683698711/2500000000000 : ℚ) : ℝ) ≤ stT212 477 := by
  have hc : ((503933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57683698711/2500000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((503933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c478 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((84113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 185823/500000) (δ := 2677/250000000) (ψ := -431649/1000000) 212 208
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t478 : ((38449491507/10000000000000 : ℚ) : ℝ) ≤ stT212 478 := by
  have hc : ((84063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).1
  have hw2 : ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((457389/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38449491507/10000000000000 : ℚ) : ℝ)
      = ((457389/10000000 : ℚ) : ℝ) * ((84063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c479 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-14047/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2412027/5000000) (δ := 2677/250000000) (ψ := -431649/1000000) 212 208
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t479 : ((-401197293/25000000000 : ℚ) : ℝ) ≤ stT212 479 := by
  have hc : ((-14049/40000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-401197293/25000000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-14049/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c480 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-718033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2964711/5000000) (δ := 2677/250000000) (ψ := -431649/1000000) 212 208
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t480 : ((-81939733047/2500000000000 : ℚ) : ℝ) ≤ stT212 480 := by
  have hc : ((-718083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81939733047/2500000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-718083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c481 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-189297/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1406481/2000000) (δ := 2677/250000000) (ψ := -431649/1000000) 212 208
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t481 : ((-86316609027/2000000000000 : ℚ) : ℝ) ≤ stT212 481 := by
  have hc : ((-189307/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86316609027/2000000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-189307/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c482 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-993771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7574801/10000000) (δ := 5301/500000000) (ψ := -431649/1000000) 212 209
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t482 : ((-7073024057/156250000000 : ℚ) : ℝ) ≤ stT212 482 := by
  have hc : ((-993821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).2
  have h0 : (0:ℝ) ≤ ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7073024057/156250000000 : ℚ) : ℝ)
      = ((7117/156250 : ℚ) : ℝ) * ((-993821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c483 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-851979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -809547/1250000) (δ := 5301/500000000) (ψ := -431649/1000000) 212 209
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t483 : ((-48460853433/1250000000000 : ℚ) : ℝ) ≤ stT212 483 := by
  have hc : ((-852029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).2
  have h0 : (0:ℝ) ≤ ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48460853433/1250000000000 : ℚ) : ℝ)
      = ((56877/1250000 : ℚ) : ℝ) * ((-852029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c484 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-54909/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5380177/10000000) (δ := 5301/500000000) (ψ := -431649/1000000) 212 209
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t484 : ((-6240234761/250000000000 : ℚ) : ℝ) ≤ stT212 484 := by
  have hc : ((-27457/50000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).2
  have h0 : (0:ℝ) ≤ ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6240234761/250000000000 : ℚ) : ℝ)
      = ((227273/5000000 : ℚ) : ℝ) * ((-27457/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c485 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-143233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -428631/1000000) (δ := 5301/500000000) (ψ := -431649/1000000) 212 209
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t485 : ((-65061514791/10000000000000 : ℚ) : ℝ) ≤ stT212 485 := by
  have hc : ((-143283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).2
  have h0 : (0:ℝ) ≤ ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65061514791/10000000000000 : ℚ) : ℝ)
      = ((454077/10000000 : ℚ) : ℝ) * ((-143283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c486 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((144389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -399327/1250000) (δ := 5301/500000000) (ψ := -431649/1000000) 212 209
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t486 : ((16371202419/1250000000000 : ℚ) : ℝ) ≤ stT212 486 := by
  have hc : ((36091/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16371202419/1250000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((36091/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c487 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((83239/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2105201/10000000) (δ := 5301/500000000) (ψ := -431649/1000000) 212 209
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t487 : ((150865352133/5000000000000 : ℚ) : ℝ) ≤ stT212 487 := by
  have hc : ((332931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150865352133/5000000000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((332931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c488 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((918231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -254503/2500000) (δ := 5301/500000000) (ψ := -431649/1000000) 212 209
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t488 : ((207820169359/5000000000000 : ℚ) : ℝ) ≤ stT212 488 := by
  have hc : ((918181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).1
  have hw2 : ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((226339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((207820169359/5000000000000 : ℚ) : ℝ)
      = ((226339/5000000 : ℚ) : ℝ) * ((918181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c489 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((499821/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33449/5000000) (δ := 5301/500000000) (ψ := -431649/1000000) 212 209
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t489 : ((11300762407/250000000000 : ℚ) : ℝ) ≤ stT212 489 := by
  have hc : ((124949/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).1
  have hw2 : ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90443/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11300762407/250000000000 : ℚ) : ℝ)
      = ((90443/2000000 : ℚ) : ℝ) * ((124949/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c490 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((896117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 229927/2000000) (δ := 5301/500000000) (ψ := -431649/1000000) 212 209
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t490 : ((404800955451/10000000000000 : ℚ) : ℝ) ≤ stT212 490 := by
  have hc : ((896067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).1
  have hw2 : ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451753/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((404800955451/10000000000000 : ℚ) : ℝ)
      = ((451753/10000000 : ℚ) : ℝ) * ((896067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c491 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((125559/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2230199/10000000) (δ := 5301/500000000) (ψ := -431649/1000000) 212 209
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t491 : ((56659384857/2000000000000 : ℚ) : ℝ) ≤ stT212 491 := by
  have hc : ((125549/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).1
  have hw2 : ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451293/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56659384857/2000000000000 : ℚ) : ℝ)
      = ((451293/10000000 : ℚ) : ℝ) * ((125549/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c492 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((122433/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3308537/10000000) (δ := 5301/500000000) (ψ := -431649/1000000) 212 209
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t492 : ((3449105517/312500000000 : ℚ) : ℝ) ≤ stT212 492 := by
  have hc : ((15301/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3449105517/312500000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((15301/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c493 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-182043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4384649/10000000) (δ := 5301/500000000) (ψ := -431649/1000000) 212 209
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t493 : ((-41005340577/5000000000000 : ℚ) : ℝ) ≤ stT212 493 := by
  have hc : ((-182093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).2
  have h0 : (0:ℝ) ≤ ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41005340577/5000000000000 : ℚ) : ℝ)
      = ((225189/5000000 : ℚ) : ℝ) * ((-182093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c494 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-287523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5458641/10000000) (δ := 5301/500000000) (ψ := -431649/1000000) 212 209
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t494 : ((-16171771407/625000000000 : ℚ) : ℝ) ≤ stT212 494 := by
  have hc : ((-71887/125000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).2
  have h0 : (0:ℝ) ≤ ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16171771407/625000000000 : ℚ) : ℝ)
      = ((224961/5000000 : ℚ) : ℝ) * ((-71887/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c495 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-172619/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6530407/10000000) (δ := 5301/500000000) (ψ := -431649/1000000) 212 209
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t495 : ((-77591038743/2000000000000 : ℚ) : ℝ) ≤ stT212 495 := by
  have hc : ((-172629/200000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).2
  have h0 : (0:ℝ) ≤ ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77591038743/2000000000000 : ℚ) : ℝ)
      = ((449467/10000000 : ℚ) : ℝ) * ((-172629/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c496 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-497423/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7600053/10000000) (δ := 5301/500000000) (ψ := -431649/1000000) 212 209
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t496 : ((-13960069767/312500000000 : ℚ) : ℝ) ≤ stT212 496 := by
  have hc : ((-62181/62500 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).2
  have h0 : (0:ℝ) ≤ ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13960069767/312500000000 : ℚ) : ℝ)
      = ((224507/5000000 : ℚ) : ℝ) * ((-62181/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c497 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-947517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7040437/10000000) (δ := 10709/1000000000) (ψ := -431649/1000000) 212 210
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t497 : ((-212521274327/5000000000000 : ℚ) : ℝ) ≤ stT212 497 := by
  have hc : ((-947567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212521274327/5000000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-947567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c498 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-9133/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5975137/10000000) (δ := 10709/1000000000) (ψ := -431649/1000000) 212 210
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t498 : ((-32743022659/1000000000000 : ℚ) : ℝ) ≤ stT212 498 := by
  have hc : ((-73069/100000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32743022659/1000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-73069/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c499 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-383873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4911957/10000000) (δ := 10709/1000000000) (ψ := -431649/1000000) 212 210
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t499 : ((-85933869013/5000000000000 : ℚ) : ℝ) ≤ stT212 499 := by
  have hc : ((-383923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85933869013/5000000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-383923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_c500 :
    |Real.cos (((212 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((30433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3850897/10000000) (δ := 10709/1000000000) (ψ := -431649/1000000) 212 210
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st212_t500 : ((13587672579/10000000000000 : ℚ) : ℝ) ≤ stT212 500 := by
  have hc : ((30383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((212 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st212_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13587672579/10000000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((30383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st212_p1 : ((908227/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT212 (i+1) := by
  rw [Finset.sum_range_one]
  exact st212_t1

theorem st212_p2 : ((2848110463/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT212 (i+1))
      = (∑ i ∈ Finset.range 1, stT212 (i+1)) + stT212 2 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 1
    simpa using h
  have hprev := st212_p1
  have hstep := st212_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p3 : ((1511710394699/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT212 (i+1))
      = (∑ i ∈ Finset.range 2, stT212 (i+1)) + stT212 3 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 2
    simpa using h
  have hprev := st212_p2
  have hstep := st212_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p4 : ((2204124144699/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT212 (i+1))
      = (∑ i ∈ Finset.range 3, stT212 (i+1)) + stT212 4 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 3
    simpa using h
  have hprev := st212_p3
  have hstep := st212_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p5 : ((1426012729923/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT212 (i+1))
      = (∑ i ∈ Finset.range 4, stT212 (i+1)) + stT212 5 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 4
    simpa using h
  have hprev := st212_p4
  have hstep := st212_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p6 : ((333679616437/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT212 (i+1))
      = (∑ i ∈ Finset.range 5, stT212 (i+1)) + stT212 6 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 5
    simpa using h
  have hprev := st212_p5
  have hstep := st212_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p7 : ((54266557313/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT212 (i+1))
      = (∑ i ∈ Finset.range 6, stT212 (i+1)) + stT212 7 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 6
    simpa using h
  have hprev := st212_p6
  have hstep := st212_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p8 : ((1510192611337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT212 (i+1))
      = (∑ i ∈ Finset.range 7, stT212 (i+1)) + stT212 8 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 7
    simpa using h
  have hprev := st212_p7
  have hstep := st212_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p9 : ((1220817925763/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT212 (i+1))
      = (∑ i ∈ Finset.range 8, stT212 (i+1)) + stT212 9 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 8
    simpa using h
  have hprev := st212_p8
  have hstep := st212_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p10 : ((263748199069/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT212 (i+1))
      = (∑ i ∈ Finset.range 9, stT212 (i+1)) + stT212 10 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 9
    simpa using h
  have hprev := st212_p9
  have hstep := st212_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p11 : ((87772198163/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT212 (i+1))
      = (∑ i ∈ Finset.range 10, stT212 (i+1)) + stT212 11 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 10
    simpa using h
  have hprev := st212_p10
  have hstep := st212_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p12 : ((806965214841/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT212 (i+1))
      = (∑ i ∈ Finset.range 11, stT212 (i+1)) + stT212 12 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 11
    simpa using h
  have hprev := st212_p11
  have hstep := st212_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p13 : ((1489467414499/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT212 (i+1))
      = (∑ i ∈ Finset.range 12, stT212 (i+1)) + stT212 13 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 12
    simpa using h
  have hprev := st212_p12
  have hstep := st212_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p14 : ((499217204019/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT212 (i+1))
      = (∑ i ∈ Finset.range 13, stT212 (i+1)) + stT212 14 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 13
    simpa using h
  have hprev := st212_p13
  have hstep := st212_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p15 : ((348940280241/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT212 (i+1))
      = (∑ i ∈ Finset.range 14, stT212 (i+1)) + stT212 15 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 14
    simpa using h
  have hprev := st212_p14
  have hstep := st212_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p16 : ((3741201247119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT212 (i+1))
      = (∑ i ∈ Finset.range 15, stT212 (i+1)) + stT212 16 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 15
    simpa using h
  have hprev := st212_p15
  have hstep := st212_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p17 : ((2489721885833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT212 (i+1))
      = (∑ i ∈ Finset.range 16, stT212 (i+1)) + stT212 17 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 16
    simpa using h
  have hprev := st212_p16
  have hstep := st212_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p18 : ((5179047977/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT212 (i+1))
      = (∑ i ∈ Finset.range 17, stT212 (i+1)) + stT212 18 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 17
    simpa using h
  have hprev := st212_p17
  have hstep := st212_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p19 : ((-734141569111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT212 (i+1))
      = (∑ i ∈ Finset.range 18, stT212 (i+1)) + stT212 19 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 18
    simpa using h
  have hprev := st212_p18
  have hstep := st212_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p20 : ((-122955663739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT212 (i+1))
      = (∑ i ∈ Finset.range 19, stT212 (i+1)) + stT212 20 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 19
    simpa using h
  have hprev := st212_p19
  have hstep := st212_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p21 : ((465545010191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT212 (i+1))
      = (∑ i ∈ Finset.range 20, stT212 (i+1)) + stT212 21 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 20
    simpa using h
  have hprev := st212_p20
  have hstep := st212_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p22 : ((-925214976401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT212 (i+1))
      = (∑ i ∈ Finset.range 21, stT212 (i+1)) + stT212 22 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 21
    simpa using h
  have hprev := st212_p21
  have hstep := st212_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p23 : ((433189614991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT212 (i+1))
      = (∑ i ∈ Finset.range 22, stT212 (i+1)) + stT212 23 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 22
    simpa using h
  have hprev := st212_p22
  have hstep := st212_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p24 : ((-184633101149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT212 (i+1))
      = (∑ i ∈ Finset.range 23, stT212 (i+1)) + stT212 24 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 23
    simpa using h
  have hprev := st212_p23
  have hstep := st212_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p25 : ((-539065773949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT212 (i+1))
      = (∑ i ∈ Finset.range 24, stT212 (i+1)) + stT212 25 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 24
    simpa using h
  have hprev := st212_p24
  have hstep := st212_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p26 : ((882925510569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT212 (i+1))
      = (∑ i ∈ Finset.range 25, stT212 (i+1)) + stT212 26 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 25
    simpa using h
  have hprev := st212_p25
  have hstep := st212_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p27 : ((151333390457/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT212 (i+1))
      = (∑ i ∈ Finset.range 26, stT212 (i+1)) + stT212 27 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 26
    simpa using h
  have hprev := st212_p26
  have hstep := st212_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p28 : ((-642291964661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT212 (i+1))
      = (∑ i ∈ Finset.range 27, stT212 (i+1)) + stT212 28 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 27
    simpa using h
  have hprev := st212_p27
  have hstep := st212_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p29 : ((-1015807120037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT212 (i+1))
      = (∑ i ∈ Finset.range 28, stT212 (i+1)) + stT212 29 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 28
    simpa using h
  have hprev := st212_p28
  have hstep := st212_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p30 : ((-586254080521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT212 (i+1))
      = (∑ i ∈ Finset.range 29, stT212 (i+1)) + stT212 30 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 29
    simpa using h
  have hprev := st212_p29
  have hstep := st212_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p31 : ((236384890857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT212 (i+1))
      = (∑ i ∈ Finset.range 30, stT212 (i+1)) + stT212 31 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 30
    simpa using h
  have hprev := st212_p30
  have hstep := st212_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p32 : ((1119682760311/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT212 (i+1))
      = (∑ i ∈ Finset.range 31, stT212 (i+1)) + stT212 32 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 31
    simpa using h
  have hprev := st212_p31
  have hstep := st212_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p33 : ((1957231891459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT212 (i+1))
      = (∑ i ∈ Finset.range 32, stT212 (i+1)) + stT212 33 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 32
    simpa using h
  have hprev := st212_p32
  have hstep := st212_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p34 : ((2770872225009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT212 (i+1))
      = (∑ i ∈ Finset.range 33, stT212 (i+1)) + stT212 34 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 33
    simpa using h
  have hprev := st212_p33
  have hstep := st212_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p35 : ((3601841160273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT212 (i+1))
      = (∑ i ∈ Finset.range 34, stT212 (i+1)) + stT212 35 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 34
    simpa using h
  have hprev := st212_p34
  have hstep := st212_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p36 : ((4428340829673/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT212 (i+1))
      = (∑ i ∈ Finset.range 35, stT212 (i+1)) + stT212 36 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 35
    simpa using h
  have hprev := st212_p35
  have hstep := st212_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p37 : ((10211254615841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT212 (i+1))
      = (∑ i ∈ Finset.range 36, stT212 (i+1)) + stT212 37 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 36
    simpa using h
  have hprev := st212_p36
  have hstep := st212_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p38 : ((10750502882651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT212 (i+1))
      = (∑ i ∈ Finset.range 37, stT212 (i+1)) + stT212 38 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 37
    simpa using h
  have hprev := st212_p37
  have hstep := st212_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p39 : ((402882036329/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT212 (i+1))
      = (∑ i ∈ Finset.range 38, stT212 (i+1)) + stT212 39 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 38
    simpa using h
  have hprev := st212_p38
  have hstep := st212_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p40 : ((852809239181/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT212 (i+1))
      = (∑ i ∈ Finset.range 39, stT212 (i+1)) + stT212 40 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 39
    simpa using h
  have hprev := st212_p39
  have hstep := st212_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p41 : ((1868748819823/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT212 (i+1))
      = (∑ i ∈ Finset.range 40, stT212 (i+1)) + stT212 41 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 40
    simpa using h
  have hprev := st212_p40
  have hstep := st212_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p42 : ((4062255166057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT212 (i+1))
      = (∑ i ∈ Finset.range 41, stT212 (i+1)) + stT212 42 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 41
    simpa using h
  have hprev := st212_p41
  have hstep := st212_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p43 : ((9630315595769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT212 (i+1))
      = (∑ i ∈ Finset.range 42, stT212 (i+1)) + stT212 43 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 42
    simpa using h
  have hprev := st212_p42
  have hstep := st212_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p44 : ((9634660372161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT212 (i+1))
      = (∑ i ∈ Finset.range 43, stT212 (i+1)) + stT212 44 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 43
    simpa using h
  have hprev := st212_p43
  have hstep := st212_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p45 : ((8146109904561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT212 (i+1))
      = (∑ i ∈ Finset.range 44, stT212 (i+1)) + stT212 45 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 44
    simpa using h
  have hprev := st212_p44
  have hstep := st212_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p46 : ((8143214143681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT212 (i+1))
      = (∑ i ∈ Finset.range 45, stT212 (i+1)) + stT212 46 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 45
    simpa using h
  have hprev := st212_p45
  have hstep := st212_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p47 : ((9585161612631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT212 (i+1))
      = (∑ i ∈ Finset.range 46, stT212 (i+1)) + stT212 47 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 46
    simpa using h
  have hprev := st212_p46
  have hstep := st212_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p48 : ((9022737163847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT212 (i+1))
      = (∑ i ∈ Finset.range 47, stT212 (i+1)) + stT212 48 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 47
    simpa using h
  have hprev := st212_p47
  have hstep := st212_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p49 : ((7968988170919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT212 (i+1))
      = (∑ i ∈ Finset.range 48, stT212 (i+1)) + stT212 49 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 48
    simpa using h
  have hprev := st212_p48
  have hstep := st212_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p50 : ((1854290577617/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT212 (i+1))
      = (∑ i ∈ Finset.range 49, stT212 (i+1)) + stT212 50 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 49
    simpa using h
  have hprev := st212_p49
  have hstep := st212_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p51 : ((113898373299/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT212 (i+1))
      = (∑ i ∈ Finset.range 50, stT212 (i+1)) + stT212 51 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 50
    simpa using h
  have hprev := st212_p50
  have hstep := st212_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p52 : ((2015015901613/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT212 (i+1))
      = (∑ i ∈ Finset.range 51, stT212 (i+1)) + stT212 52 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 51
    simpa using h
  have hprev := st212_p51
  have hstep := st212_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p53 : ((4704863335651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT212 (i+1))
      = (∑ i ∈ Finset.range 52, stT212 (i+1)) + stT212 53 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 52
    simpa using h
  have hprev := st212_p52
  have hstep := st212_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p54 : ((4341702569361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT212 (i+1))
      = (∑ i ∈ Finset.range 53, stT212 (i+1)) + stT212 54 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 53
    simpa using h
  have hprev := st212_p53
  have hstep := st212_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p55 : ((4217344356761/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT212 (i+1))
      = (∑ i ∈ Finset.range 54, stT212 (i+1)) + stT212 55 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 54
    simpa using h
  have hprev := st212_p54
  have hstep := st212_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p56 : ((4725315692847/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT212 (i+1))
      = (∑ i ∈ Finset.range 55, stT212 (i+1)) + stT212 56 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 55
    simpa using h
  have hprev := st212_p55
  have hstep := st212_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p57 : ((8132166071367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT212 (i+1))
      = (∑ i ∈ Finset.range 56, stT212 (i+1)) + stT212 57 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 56
    simpa using h
  have hprev := st212_p56
  have hstep := st212_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p58 : ((9314908469367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT212 (i+1))
      = (∑ i ∈ Finset.range 57, stT212 (i+1)) + stT212 58 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 57
    simpa using h
  have hprev := st212_p57
  have hstep := st212_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p59 : ((8538208706707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT212 (i+1))
      = (∑ i ∈ Finset.range 58, stT212 (i+1)) + stT212 59 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 58
    simpa using h
  have hprev := st212_p58
  have hstep := st212_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p60 : ((8816947221247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT212 (i+1))
      = (∑ i ∈ Finset.range 59, stT212 (i+1)) + stT212 60 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 59
    simpa using h
  have hprev := st212_p59
  have hstep := st212_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p61 : ((9001815715663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT212 (i+1))
      = (∑ i ∈ Finset.range 60, stT212 (i+1)) + stT212 61 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 60
    simpa using h
  have hprev := st212_p60
  have hstep := st212_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p62 : ((8448685394593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT212 (i+1))
      = (∑ i ∈ Finset.range 61, stT212 (i+1)) + stT212 62 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 61
    simpa using h
  have hprev := st212_p61
  have hstep := st212_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p63 : ((4630644870689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT212 (i+1))
      = (∑ i ∈ Finset.range 62, stT212 (i+1)) + stT212 63 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 62
    simpa using h
  have hprev := st212_p62
  have hstep := st212_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p64 : ((4141766979587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT212 (i+1))
      = (∑ i ∈ Finset.range 63, stT212 (i+1)) + stT212 64 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 63
    simpa using h
  have hprev := st212_p63
  have hstep := st212_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p65 : ((9355289273893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT212 (i+1))
      = (∑ i ∈ Finset.range 64, stT212 (i+1)) + stT212 65 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 64
    simpa using h
  have hprev := st212_p64
  have hstep := st212_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p66 : ((4118766760379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT212 (i+1))
      = (∑ i ∈ Finset.range 65, stT212 (i+1)) + stT212 66 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 65
    simpa using h
  have hprev := st212_p65
  have hstep := st212_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p67 : ((1171169811053/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT212 (i+1))
      = (∑ i ∈ Finset.range 66, stT212 (i+1)) + stT212 67 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 66
    simpa using h
  have hprev := st212_p66
  have hstep := st212_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p68 : ((1649225095757/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT212 (i+1))
      = (∑ i ∈ Finset.range 67, stT212 (i+1)) + stT212 68 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 67
    simpa using h
  have hprev := st212_p67
  have hstep := st212_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p69 : ((9338688010543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT212 (i+1))
      = (∑ i ∈ Finset.range 68, stT212 (i+1)) + stT212 69 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 68
    simpa using h
  have hprev := st212_p68
  have hstep := st212_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p70 : ((8304038026693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT212 (i+1))
      = (∑ i ∈ Finset.range 69, stT212 (i+1)) + stT212 70 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 69
    simpa using h
  have hprev := st212_p69
  have hstep := st212_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p71 : ((1848464265333/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT212 (i+1))
      = (∑ i ∈ Finset.range 70, stT212 (i+1)) + stT212 71 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 70
    simpa using h
  have hprev := st212_p70
  have hstep := st212_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p72 : ((8451624627529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT212 (i+1))
      = (∑ i ∈ Finset.range 71, stT212 (i+1)) + stT212 72 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 71
    simpa using h
  have hprev := st212_p71
  have hstep := st212_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p73 : ((4515532926677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT212 (i+1))
      = (∑ i ∈ Finset.range 72, stT212 (i+1)) + stT212 73 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 72
    simpa using h
  have hprev := st212_p72
  have hstep := st212_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p74 : ((2182822152387/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT212 (i+1))
      = (∑ i ∈ Finset.range 73, stT212 (i+1)) + stT212 74 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 73
    simpa using h
  have hprev := st212_p73
  have hstep := st212_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p75 : ((271583896987/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT212 (i+1))
      = (∑ i ∈ Finset.range 74, stT212 (i+1)) + stT212 75 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 74
    simpa using h
  have hprev := st212_p74
  have hstep := st212_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p76 : ((4552036057229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT212 (i+1))
      = (∑ i ∈ Finset.range 75, stT212 (i+1)) + stT212 76 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 75
    simpa using h
  have hprev := st212_p75
  have hstep := st212_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p77 : ((833640160389/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT212 (i+1))
      = (∑ i ∈ Finset.range 76, stT212 (i+1)) + stT212 77 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 76
    simpa using h
  have hprev := st212_p76
  have hstep := st212_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p78 : ((2341893265363/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT212 (i+1))
      = (∑ i ∈ Finset.range 77, stT212 (i+1)) + stT212 78 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 77
    simpa using h
  have hprev := st212_p77
  have hstep := st212_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p79 : ((412127965863/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT212 (i+1))
      = (∑ i ∈ Finset.range 78, stT212 (i+1)) + stT212 79 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 78
    simpa using h
  have hprev := st212_p78
  have hstep := st212_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p80 : ((9228913744619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT212 (i+1))
      = (∑ i ∈ Finset.range 79, stT212 (i+1)) + stT212 80 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 79
    simpa using h
  have hprev := st212_p79
  have hstep := st212_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p81 : ((8626792151811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT212 (i+1))
      = (∑ i ∈ Finset.range 80, stT212 (i+1)) + stT212 81 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 80
    simpa using h
  have hprev := st212_p80
  have hstep := st212_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p82 : ((8662417353711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT212 (i+1))
      = (∑ i ∈ Finset.range 81, stT212 (i+1)) + stT212 82 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 81
    simpa using h
  have hprev := st212_p81
  have hstep := st212_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p83 : ((369050690719/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT212 (i+1))
      = (∑ i ∈ Finset.range 82, stT212 (i+1)) + stT212 83 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 82
    simpa using h
  have hprev := st212_p82
  have hstep := st212_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p84 : ((1646763233667/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT212 (i+1))
      = (∑ i ∈ Finset.range 83, stT212 (i+1)) + stT212 84 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 83
    simpa using h
  have hprev := st212_p83
  have hstep := st212_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p85 : ((9295904152779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT212 (i+1))
      = (∑ i ∈ Finset.range 84, stT212 (i+1)) + stT212 85 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 84
    simpa using h
  have hprev := st212_p84
  have hstep := st212_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p86 : ((8597325532899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT212 (i+1))
      = (∑ i ∈ Finset.range 85, stT212 (i+1)) + stT212 86 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 85
    simpa using h
  have hprev := st212_p85
  have hstep := st212_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p87 : ((8612271846291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT212 (i+1))
      = (∑ i ∈ Finset.range 86, stT212 (i+1)) + stT212 87 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 86
    simpa using h
  have hprev := st212_p86
  have hstep := st212_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p88 : ((1860558895519/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT212 (i+1))
      = (∑ i ∈ Finset.range 87, stT212 (i+1)) + stT212 88 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 87
    simpa using h
  have hprev := st212_p87
  have hstep := st212_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p89 : ((8250363803317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT212 (i+1))
      = (∑ i ∈ Finset.range 88, stT212 (i+1)) + stT212 89 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 88
    simpa using h
  have hprev := st212_p88
  have hstep := st212_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p90 : ((9087620646181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT212 (i+1))
      = (∑ i ∈ Finset.range 89, stT212 (i+1)) + stT212 90 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 89
    simpa using h
  have hprev := st212_p89
  have hstep := st212_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p91 : ((8963220665231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT212 (i+1))
      = (∑ i ∈ Finset.range 90, stT212 (i+1)) + stT212 91 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 90
    simpa using h
  have hprev := st212_p90
  have hstep := st212_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p92 : ((1035870373349/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT212 (i+1))
      = (∑ i ∈ Finset.range 91, stT212 (i+1)) + stT212 92 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 91
    simpa using h
  have hprev := st212_p91
  have hstep := st212_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p93 : ((582733736189/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT212 (i+1))
      = (∑ i ∈ Finset.range 92, stT212 (i+1)) + stT212 93 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 92
    simpa using h
  have hprev := st212_p92
  have hstep := st212_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p94 : ((2162454739611/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT212 (i+1))
      = (∑ i ∈ Finset.range 93, stT212 (i+1)) + stT212 94 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 93
    simpa using h
  have hprev := st212_p93
  have hstep := st212_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p95 : ((422991613557/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT212 (i+1))
      = (∑ i ∈ Finset.range 94, stT212 (i+1)) + stT212 95 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 94
    simpa using h
  have hprev := st212_p94
  have hstep := st212_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p96 : ((9372984047/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT212 (i+1))
      = (∑ i ∈ Finset.range 95, stT212 (i+1)) + stT212 96 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 95
    simpa using h
  have hprev := st212_p95
  have hstep := st212_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p97 : ((8473152059843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT212 (i+1))
      = (∑ i ∈ Finset.range 96, stT212 (i+1)) + stT212 97 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 96
    simpa using h
  have hprev := st212_p96
  have hstep := st212_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p98 : ((1719171246687/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT212 (i+1))
      = (∑ i ∈ Finset.range 97, stT212 (i+1)) + stT212 98 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 97
    simpa using h
  have hprev := st212_p97
  have hstep := st212_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p99 : ((1872467530223/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT212 (i+1))
      = (∑ i ∈ Finset.range 98, stT212 (i+1)) + stT212 99 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 98
    simpa using h
  have hprev := st212_p98
  have hstep := st212_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p100 : ((1681844530223/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT212 (i+1))
      = (∑ i ∈ Finset.range 99, stT212 (i+1)) + stT212 100 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 99
    simpa using h
  have hprev := st212_p99
  have hstep := st212_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p101 : ((1079634894857/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT212 (i+1))
      = (∑ i ∈ Finset.range 100, stT212 (i+1)) + stT212 101 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 100
    simpa using h
  have hprev := st212_p100
  have hstep := st212_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p102 : ((4681096755683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT212 (i+1))
      = (∑ i ∈ Finset.range 101, stT212 (i+1)) + stT212 102 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 101
    simpa using h
  have hprev := st212_p101
  have hstep := st212_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p103 : ((1053522560387/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT212 (i+1))
      = (∑ i ∈ Finset.range 102, stT212 (i+1)) + stT212 103 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 102
    simpa using h
  have hprev := st212_p102
  have hstep := st212_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p104 : ((1072222711277/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT212 (i+1))
      = (∑ i ∈ Finset.range 103, stT212 (i+1)) + stT212 104 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 103
    simpa using h
  have hprev := st212_p103
  have hstep := st212_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p105 : ((2344246065079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT212 (i+1))
      = (∑ i ∈ Finset.range 104, stT212 (i+1)) + stT212 105 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 104
    simpa using h
  have hprev := st212_p104
  have hstep := st212_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p106 : ((4267248791459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT212 (i+1))
      = (∑ i ∈ Finset.range 105, stT212 (i+1)) + stT212 106 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 105
    simpa using h
  have hprev := st212_p105
  have hstep := st212_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p107 : ((8436861979603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT212 (i+1))
      = (∑ i ∈ Finset.range 106, stT212 (i+1)) + stT212 107 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 106
    simpa using h
  have hprev := st212_p106
  have hstep := st212_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p108 : ((9356031084853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT212 (i+1))
      = (∑ i ∈ Finset.range 107, stT212 (i+1)) + stT212 108 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 107
    simpa using h
  have hprev := st212_p107
  have hstep := st212_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p109 : ((8751239960513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT212 (i+1))
      = (∑ i ∈ Finset.range 108, stT212 (i+1)) + stT212 109 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 108
    simpa using h
  have hprev := st212_p108
  have hstep := st212_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p110 : ((4137814389769/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT212 (i+1))
      = (∑ i ∈ Finset.range 109, stT212 (i+1)) + stT212 110 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 109
    simpa using h
  have hprev := st212_p109
  have hstep := st212_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p111 : ((4605169804999/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT212 (i+1))
      = (∑ i ∈ Finset.range 110, stT212 (i+1)) + stT212 111 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 110
    simpa using h
  have hprev := st212_p110
  have hstep := st212_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p112 : ((4531674077183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT212 (i+1))
      = (∑ i ∈ Finset.range 111, stT212 (i+1)) + stT212 112 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 111
    simpa using h
  have hprev := st212_p111
  have hstep := st212_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p113 : ((1644901259589/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT212 (i+1))
      = (∑ i ∈ Finset.range 112, stT212 (i+1)) + stT212 113 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 112
    simpa using h
  have hprev := st212_p112
  have hstep := st212_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p114 : ((35497359513/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT212 (i+1))
      = (∑ i ∈ Finset.range 113, stT212 (i+1)) + stT212 114 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 113
    simpa using h
  have hprev := st212_p113
  have hstep := st212_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p115 : ((4670103843301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT212 (i+1))
      = (∑ i ∈ Finset.range 114, stT212 (i+1)) + stT212 115 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 114
    simpa using h
  have hprev := st212_p114
  have hstep := st212_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p116 : ((8442529197169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT212 (i+1))
      = (∑ i ∈ Finset.range 115, stT212 (i+1)) + stT212 116 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 115
    simpa using h
  have hprev := st212_p115
  have hstep := st212_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p117 : ((8433689118607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT212 (i+1))
      = (∑ i ∈ Finset.range 116, stT212 (i+1)) + stT212 117 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 116
    simpa using h
  have hprev := st212_p116
  have hstep := st212_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p118 : ((9331226674831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT212 (i+1))
      = (∑ i ∈ Finset.range 117, stT212 (i+1)) + stT212 118 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 117
    simpa using h
  have hprev := st212_p117
  have hstep := st212_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p119 : ((8938907003801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT212 (i+1))
      = (∑ i ∈ Finset.range 118, stT212 (i+1)) + stT212 119 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 118
    simpa using h
  have hprev := st212_p118
  have hstep := st212_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p120 : ((4104823156193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT212 (i+1))
      = (∑ i ∈ Finset.range 119, stT212 (i+1)) + stT212 120 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 119
    simpa using h
  have hprev := st212_p119
  have hstep := st212_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p121 : ((4441454637743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT212 (i+1))
      = (∑ i ∈ Finset.range 120, stT212 (i+1)) + stT212 121 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 120
    simpa using h
  have hprev := st212_p120
  have hstep := st212_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p122 : ((1170731279821/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT212 (i+1))
      = (∑ i ∈ Finset.range 121, stT212 (i+1)) + stT212 122 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 121
    simpa using h
  have hprev := st212_p121
  have hstep := st212_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p123 : ((4268163681809/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT212 (i+1))
      = (∑ i ∈ Finset.range 122, stT212 (i+1)) + stT212 123 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 122
    simpa using h
  have hprev := st212_p122
  have hstep := st212_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p124 : ((1661591999109/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT212 (i+1))
      = (∑ i ∈ Finset.range 123, stT212 (i+1)) + stT212 124 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 123
    simpa using h
  have hprev := st212_p123
  have hstep := st212_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p125 : ((4597679741303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT212 (i+1))
      = (∑ i ∈ Finset.range 124, stT212 (i+1)) + stT212 125 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 124
    simpa using h
  have hprev := st212_p124
  have hstep := st212_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p126 : ((2300293993209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT212 (i+1))
      = (∑ i ∈ Finset.range 125, stT212 (i+1)) + stT212 126 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 125
    simpa using h
  have hprev := st212_p125
  have hstep := st212_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p127 : ((4159038255861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT212 (i+1))
      = (∑ i ∈ Finset.range 126, stT212 (i+1)) + stT212 127 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 126
    simpa using h
  have hprev := st212_p126
  have hstep := st212_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p128 : ((4242683639683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT212 (i+1))
      = (∑ i ∈ Finset.range 127, stT212 (i+1)) + stT212 128 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 127
    simpa using h
  have hprev := st212_p127
  have hstep := st212_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p129 : ((2333498353529/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT212 (i+1))
      = (∑ i ∈ Finset.range 128, stT212 (i+1)) + stT212 129 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 128
    simpa using h
  have hprev := st212_p128
  have hstep := st212_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p130 : ((4522482818569/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT212 (i+1))
      = (∑ i ∈ Finset.range 129, stT212 (i+1)) + stT212 130 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 129
    simpa using h
  have hprev := st212_p129
  have hstep := st212_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p131 : ((8236660077503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT212 (i+1))
      = (∑ i ∈ Finset.range 130, stT212 (i+1)) + stT212 131 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 130
    simpa using h
  have hprev := st212_p130
  have hstep := st212_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p132 : ((8600154125227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT212 (i+1))
      = (∑ i ∈ Finset.range 131, stT212 (i+1)) + stT212 132 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 131
    simpa using h
  have hprev := st212_p131
  have hstep := st212_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p133 : ((1172131246497/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT212 (i+1))
      = (∑ i ∈ Finset.range 132, stT212 (i+1)) + stT212 133 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 132
    simpa using h
  have hprev := st212_p132
  have hstep := st212_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p134 : ((8980149679271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT212 (i+1))
      = (∑ i ∈ Finset.range 133, stT212 (i+1)) + stT212 134 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 133
    simpa using h
  have hprev := st212_p133
  have hstep := st212_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p135 : ((1643557977161/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT212 (i+1))
      = (∑ i ∈ Finset.range 134, stT212 (i+1)) + stT212 135 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 134
    simpa using h
  have hprev := st212_p134
  have hstep := st212_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p136 : ((8611064014241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT212 (i+1))
      = (∑ i ∈ Finset.range 135, stT212 (i+1)) + stT212 136 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 135
    simpa using h
  have hprev := st212_p135
  have hstep := st212_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p137 : ((4688503085691/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT212 (i+1))
      = (∑ i ∈ Finset.range 136, stT212 (i+1)) + stT212 137 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 136
    simpa using h
  have hprev := st212_p136
  have hstep := st212_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p138 : ((9022203105039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT212 (i+1))
      = (∑ i ∈ Finset.range 137, stT212 (i+1)) + stT212 138 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 137
    simpa using h
  have hprev := st212_p137
  have hstep := st212_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p139 : ((4118795055767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT212 (i+1))
      = (∑ i ∈ Finset.range 138, stT212 (i+1)) + stT212 139 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 138
    simpa using h
  have hprev := st212_p138
  have hstep := st212_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p140 : ((4259179360937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT212 (i+1))
      = (∑ i ∈ Finset.range 139, stT212 (i+1)) + stT212 140 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 139
    simpa using h
  have hprev := st212_p139
  have hstep := st212_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p141 : ((9328412820811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT212 (i+1))
      = (∑ i ∈ Finset.range 140, stT212 (i+1)) + stT212 141 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 140
    simpa using h
  have hprev := st212_p140
  have hstep := st212_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p142 : ((9158164611743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT212 (i+1))
      = (∑ i ∈ Finset.range 141, stT212 (i+1)) + stT212 142 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 141
    simpa using h
  have hprev := st212_p141
  have hstep := st212_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p143 : ((1041001496189/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT212 (i+1))
      = (∑ i ∈ Finset.range 142, stT212 (i+1)) + stT212 143 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 142
    simpa using h
  have hprev := st212_p142
  have hstep := st212_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p144 : ((8351069460289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT212 (i+1))
      = (∑ i ∈ Finset.range 143, stT212 (i+1)) + stT212 144 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 143
    simpa using h
  have hprev := st212_p143
  have hstep := st212_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p145 : ((1835817879923/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT212 (i+1))
      = (∑ i ∈ Finset.range 144, stT212 (i+1)) + stT212 145 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 144
    simpa using h
  have hprev := st212_p144
  have hstep := st212_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p146 : ((1867015940087/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT212 (i+1))
      = (∑ i ∈ Finset.range 145, stT212 (i+1)) + stT212 146 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 145
    simpa using h
  have hprev := st212_p145
  have hstep := st212_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p147 : ((2137604853193/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT212 (i+1))
      = (∑ i ∈ Finset.range 146, stT212 (i+1)) + stT212 147 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 146
    simpa using h
  have hprev := st212_p146
  have hstep := st212_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p148 : ((8195153995767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT212 (i+1))
      = (∑ i ∈ Finset.range 147, stT212 (i+1)) + stT212 148 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 147
    simpa using h
  have hprev := st212_p147
  have hstep := st212_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p149 : ((355033072731/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT212 (i+1))
      = (∑ i ∈ Finset.range 148, stT212 (i+1)) + stT212 149 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 148
    simpa using h
  have hprev := st212_p148
  have hstep := st212_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p150 : ((9428019797091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT212 (i+1))
      = (∑ i ∈ Finset.range 149, stT212 (i+1)) + stT212 150 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 149
    simpa using h
  have hprev := st212_p149
  have hstep := st212_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p151 : ((892526990457/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT212 (i+1))
      = (∑ i ∈ Finset.range 150, stT212 (i+1)) + stT212 151 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 150
    simpa using h
  have hprev := st212_p150
  have hstep := st212_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p152 : ((4105627388301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT212 (i+1))
      = (∑ i ∈ Finset.range 151, stT212 (i+1)) + stT212 152 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 151
    simpa using h
  have hprev := st212_p151
  have hstep := st212_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p153 : ((846075438213/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT212 (i+1))
      = (∑ i ∈ Finset.range 152, stT212 (i+1)) + stT212 153 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 152
    simpa using h
  have hprev := st212_p152
  have hstep := st212_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p154 : ((4630168854103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT212 (i+1))
      = (∑ i ∈ Finset.range 153, stT212 (i+1)) + stT212 154 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 153
    simpa using h
  have hprev := st212_p153
  have hstep := st212_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p155 : ((9320096398587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT212 (i+1))
      = (∑ i ∈ Finset.range 154, stT212 (i+1)) + stT212 155 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 154
    simpa using h
  have hprev := st212_p154
  have hstep := st212_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p156 : ((4275515939493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT212 (i+1))
      = (∑ i ∈ Finset.range 155, stT212 (i+1)) + stT212 156 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 155
    simpa using h
  have hprev := st212_p155
  have hstep := st212_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p157 : ((8169684362037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT212 (i+1))
      = (∑ i ∈ Finset.range 156, stT212 (i+1)) + stT212 157 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 156
    simpa using h
  have hprev := st212_p156
  have hstep := st212_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p158 : ((8766231187373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT212 (i+1))
      = (∑ i ∈ Finset.range 157, stT212 (i+1)) + stT212 158 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 157
    simpa using h
  have hprev := st212_p157
  have hstep := st212_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p159 : ((9414088824191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT212 (i+1))
      = (∑ i ∈ Finset.range 158, stT212 (i+1)) + stT212 159 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 158
    simpa using h
  have hprev := st212_p158
  have hstep := st212_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p160 : ((9125941080021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT212 (i+1))
      = (∑ i ∈ Finset.range 159, stT212 (i+1)) + stT212 160 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 159
    simpa using h
  have hprev := st212_p159
  have hstep := st212_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p161 : ((8343753522297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT212 (i+1))
      = (∑ i ∈ Finset.range 160, stT212 (i+1)) + stT212 161 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 160
    simpa using h
  have hprev := st212_p160
  have hstep := st212_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p162 : ((8237968668947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT212 (i+1))
      = (∑ i ∈ Finset.range 161, stT212 (i+1)) + stT212 162 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 161
    simpa using h
  have hprev := st212_p161
  have hstep := st212_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p163 : ((8959001794987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT212 (i+1))
      = (∑ i ∈ Finset.range 162, stT212 (i+1)) + stT212 163 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 162
    simpa using h
  have hprev := st212_p162
  have hstep := st212_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p164 : ((9447127847863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT212 (i+1))
      = (∑ i ∈ Finset.range 163, stT212 (i+1)) + stT212 164 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 163
    simpa using h
  have hprev := st212_p163
  have hstep := st212_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p165 : ((2249733963269/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT212 (i+1))
      = (∑ i ∈ Finset.range 164, stT212 (i+1)) + stT212 165 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 164
    simpa using h
  have hprev := st212_p164
  have hstep := st212_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p166 : ((330521100251/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT212 (i+1))
      = (∑ i ∈ Finset.range 165, stT212 (i+1)) + stT212 166 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 165
    simpa using h
  have hprev := st212_p165
  have hstep := st212_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p167 : ((2070792723197/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT212 (i+1))
      = (∑ i ∈ Finset.range 166, stT212 (i+1)) + stT212 167 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 166
    simpa using h
  have hprev := st212_p166
  have hstep := st212_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p168 : ((225620094089/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT212 (i+1))
      = (∑ i ∈ Finset.range 167, stT212 (i+1)) + stT212 168 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 167
    simpa using h
  have hprev := st212_p167
  have hstep := st212_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p169 : ((94538017961/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT212 (i+1))
      = (∑ i ∈ Finset.range 168, stT212 (i+1)) + stT212 169 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 168
    simpa using h
  have hprev := st212_p168
  have hstep := st212_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p170 : ((1796818037623/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT212 (i+1))
      = (∑ i ∈ Finset.range 169, stT212 (i+1)) + stT212 170 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 169
    simpa using h
  have hprev := st212_p169
  have hstep := st212_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p171 : ((1652201838423/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT212 (i+1))
      = (∑ i ∈ Finset.range 170, stT212 (i+1)) + stT212 171 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 170
    simpa using h
  have hprev := st212_p170
  have hstep := st212_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p172 : ((825870265079/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT212 (i+1))
      = (∑ i ∈ Finset.range 171, stT212 (i+1)) + stT212 172 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 171
    simpa using h
  have hprev := st212_p171
  have hstep := st212_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p173 : ((224355133593/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT212 (i+1))
      = (∑ i ∈ Finset.range 172, stT212 (i+1)) + stT212 173 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 172
    simpa using h
  have hprev := st212_p172
  have hstep := st212_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p174 : ((4729435899491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT212 (i+1))
      = (∑ i ∈ Finset.range 173, stT212 (i+1)) + stT212 174 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 173
    simpa using h
  have hprev := st212_p173
  have hstep := st212_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p175 : ((227060516721/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT212 (i+1))
      = (∑ i ∈ Finset.range 174, stT212 (i+1)) + stT212 175 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 174
    simpa using h
  have hprev := st212_p174
  have hstep := st212_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p176 : ((8338042046749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT212 (i+1))
      = (∑ i ∈ Finset.range 175, stT212 (i+1)) + stT212 176 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 175
    simpa using h
  have hprev := st212_p175
  have hstep := st212_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p177 : ((2045101847389/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT212 (i+1))
      = (∑ i ∈ Finset.range 176, stT212 (i+1)) + stT212 177 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 176
    simpa using h
  have hprev := st212_p176
  have hstep := st212_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p178 : ((4402078297161/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT212 (i+1))
      = (∑ i ∈ Finset.range 177, stT212 (i+1)) + stT212 178 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 177
    simpa using h
  have hprev := st212_p177
  have hstep := st212_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p179 : ((588812204157/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT212 (i+1))
      = (∑ i ∈ Finset.range 178, stT212 (i+1)) + stT212 179 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 178
    simpa using h
  have hprev := st212_p178
  have hstep := st212_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p180 : ((144771560013/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT212 (i+1))
      = (∑ i ∈ Finset.range 179, stT212 (i+1)) + stT212 180 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 179
    simpa using h
  have hprev := st212_p179
  have hstep := st212_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p181 : ((4267434014121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT212 (i+1))
      = (∑ i ∈ Finset.range 180, stT212 (i+1)) + stT212 181 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 180
    simpa using h
  have hprev := st212_p180
  have hstep := st212_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p182 : ((2030798336123/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT212 (i+1))
      = (∑ i ∈ Finset.range 181, stT212 (i+1)) + stT212 182 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 181
    simpa using h
  have hprev := st212_p181
  have hstep := st212_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p183 : ((8523863693249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT212 (i+1))
      = (∑ i ∈ Finset.range 182, stT212 (i+1)) + stT212 183 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 182
    simpa using h
  have hprev := st212_p182
  have hstep := st212_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p184 : ((9251920980723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT212 (i+1))
      = (∑ i ∈ Finset.range 183, stT212 (i+1)) + stT212 184 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 183
    simpa using h
  have hprev := st212_p183
  have hstep := st212_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p185 : ((9443961818379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT212 (i+1))
      = (∑ i ∈ Finset.range 184, stT212 (i+1)) + stT212 185 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 184
    simpa using h
  have hprev := st212_p184
  have hstep := st212_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p186 : ((8879480083779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT212 (i+1))
      = (∑ i ∈ Finset.range 185, stT212 (i+1)) + stT212 186 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 185
    simpa using h
  have hprev := st212_p185
  have hstep := st212_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p187 : ((8219223929901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT212 (i+1))
      = (∑ i ∈ Finset.range 186, stT212 (i+1)) + stT212 187 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 186
    simpa using h
  have hprev := st212_p186
  have hstep := st212_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p188 : ((8222352729861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT212 (i+1))
      = (∑ i ∈ Finset.range 187, stT212 (i+1)) + stT212 188 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 187
    simpa using h
  have hprev := st212_p187
  have hstep := st212_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p189 : ((8879874363909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT212 (i+1))
      = (∑ i ∈ Finset.range 188, stT212 (i+1)) + stT212 189 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 188
    simpa using h
  have hprev := st212_p188
  have hstep := st212_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p190 : ((9445337926397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT212 (i+1))
      = (∑ i ∈ Finset.range 189, stT212 (i+1)) + stT212 190 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 189
    simpa using h
  have hprev := st212_p189
  have hstep := st212_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p191 : ((9288084818797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT212 (i+1))
      = (∑ i ∈ Finset.range 190, stT212 (i+1)) + stT212 191 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 190
    simpa using h
  have hprev := st212_p190
  have hstep := st212_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p192 : ((8587864871733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT212 (i+1))
      = (∑ i ∈ Finset.range 191, stT212 (i+1)) + stT212 192 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 191
    simpa using h
  have hprev := st212_p191
  have hstep := st212_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p193 : ((8116324927189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT212 (i+1))
      = (∑ i ∈ Finset.range 192, stT212 (i+1)) + stT212 193 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 192
    simpa using h
  have hprev := st212_p192
  have hstep := st212_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p194 : ((8383519458511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT212 (i+1))
      = (∑ i ∈ Finset.range 193, stT212 (i+1)) + stT212 194 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 193
    simpa using h
  have hprev := st212_p193
  have hstep := st212_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p195 : ((1819212153153/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT212 (i+1))
      = (∑ i ∈ Finset.range 194, stT212 (i+1)) + stT212 195 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 194
    simpa using h
  have hprev := st212_p194
  have hstep := st212_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p196 : ((1898188931319/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT212 (i+1))
      = (∑ i ∈ Finset.range 195, stT212 (i+1)) + stT212 196 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 195
    simpa using h
  have hprev := st212_p195
  have hstep := st212_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p197 : ((9153677984499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT212 (i+1))
      = (∑ i ∈ Finset.range 196, stT212 (i+1)) + stT212 197 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 196
    simpa using h
  have hprev := st212_p196
  have hstep := st212_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p198 : ((8442978847029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT212 (i+1))
      = (∑ i ∈ Finset.range 197, stT212 (i+1)) + stT212 198 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 197
    simpa using h
  have hprev := st212_p197
  have hstep := st212_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p199 : ((8098681239567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT212 (i+1))
      = (∑ i ∈ Finset.range 198, stT212 (i+1)) + stT212 199 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 198
    simpa using h
  have hprev := st212_p198
  have hstep := st212_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p200 : ((8471583488151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT212 (i+1))
      = (∑ i ∈ Finset.range 199, stT212 (i+1)) + stT212 200 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 199
    simpa using h
  have hprev := st212_p199
  have hstep := st212_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p201 : ((4588133789943/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT212 (i+1))
      = (∑ i ∈ Finset.range 200, stT212 (i+1)) + stT212 201 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 200
    simpa using h
  have hprev := st212_p200
  have hstep := st212_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p202 : ((9498999784219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT212 (i+1))
      = (∑ i ∈ Finset.range 201, stT212 (i+1)) + stT212 202 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 201
    simpa using h
  have hprev := st212_p201
  have hstep := st212_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p203 : ((9120013416383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT212 (i+1))
      = (∑ i ∈ Finset.range 202, stT212 (i+1)) + stT212 203 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 202
    simpa using h
  have hprev := st212_p202
  have hstep := st212_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p204 : ((4210217314803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT212 (i+1))
      = (∑ i ∈ Finset.range 203, stT212 (i+1)) + stT212 204 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 203
    simpa using h
  have hprev := st212_p203
  have hstep := st212_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p205 : ((8089975494111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT212 (i+1))
      = (∑ i ∈ Finset.range 204, stT212 (i+1)) + stT212 205 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 204
    simpa using h
  have hprev := st212_p204
  have hstep := st212_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p206 : ((1055932343177/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT212 (i+1))
      = (∑ i ∈ Finset.range 205, stT212 (i+1)) + stT212 206 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 205
    simpa using h
  have hprev := st212_p205
  have hstep := st212_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p207 : ((1142807782793/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT212 (i+1))
      = (∑ i ∈ Finset.range 206, stT212 (i+1)) + stT212 207 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 206
    simpa using h
  have hprev := st212_p206
  have hstep := st212_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p208 : ((4753732284797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT212 (i+1))
      = (∑ i ∈ Finset.range 207, stT212 (i+1)) + stT212 208 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 207
    simpa using h
  have hprev := st212_p207
  have hstep := st212_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p209 : ((287465112217/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT212 (i+1))
      = (∑ i ∈ Finset.range 208, stT212 (i+1)) + stT212 209 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 208
    simpa using h
  have hprev := st212_p208
  have hstep := st212_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p210 : ((2127998318669/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT212 (i+1))
      = (∑ i ∈ Finset.range 209, stT212 (i+1)) + stT212 210 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 209
    simpa using h
  have hprev := st212_p209
  have hstep := st212_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p211 : ((1617956091481/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT212 (i+1))
      = (∑ i ∈ Finset.range 210, stT212 (i+1)) + stT212 211 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 210
    simpa using h
  have hprev := st212_p210
  have hstep := st212_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p212 : ((8320203215207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT212 (i+1))
      = (∑ i ∈ Finset.range 211, stT212 (i+1)) + stT212 212 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 211
    simpa using h
  have hprev := st212_p211
  have hstep := st212_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p213 : ((8987163844031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT212 (i+1))
      = (∑ i ∈ Finset.range 212, stT212 (i+1)) + stT212 213 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 212
    simpa using h
  have hprev := st212_p212
  have hstep := st212_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p214 : ((1185207372407/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT212 (i+1))
      = (∑ i ∈ Finset.range 213, stT212 (i+1)) + stT212 214 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 213
    simpa using h
  have hprev := st212_p213
  have hstep := st212_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p215 : ((9359810342581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT212 (i+1))
      = (∑ i ∈ Finset.range 214, stT212 (i+1)) + stT212 215 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 214
    simpa using h
  have hprev := st212_p214
  have hstep := st212_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p216 : ((8735065774819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT212 (i+1))
      = (∑ i ∈ Finset.range 215, stT212 (i+1)) + stT212 216 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 215
    simpa using h
  have hprev := st212_p215
  have hstep := st212_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p217 : ((2041038773321/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT212 (i+1))
      = (∑ i ∈ Finset.range 216, stT212 (i+1)) + stT212 217 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 216
    simpa using h
  have hprev := st212_p216
  have hstep := st212_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p218 : ((1018455526897/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT212 (i+1))
      = (∑ i ∈ Finset.range 217, stT212 (i+1)) + stT212 218 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 217
    simpa using h
  have hprev := st212_p217
  have hstep := st212_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p219 : ((217391537907/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT212 (i+1))
      = (∑ i ∈ Finset.range 218, stT212 (i+1)) + stT212 219 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 218
    simpa using h
  have hprev := st212_p218
  have hstep := st212_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p220 : ((9331015192497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT212 (i+1))
      = (∑ i ∈ Finset.range 219, stT212 (i+1)) + stT212 220 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 219
    simpa using h
  have hprev := st212_p219
  have hstep := st212_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p221 : ((9509347266417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT212 (i+1))
      = (∑ i ∈ Finset.range 220, stT212 (i+1)) + stT212 221 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 220
    simpa using h
  have hprev := st212_p220
  have hstep := st212_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p222 : ((4541378931873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT212 (i+1))
      = (∑ i ∈ Finset.range 221, stT212 (i+1)) + stT212 222 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 221
    simpa using h
  have hprev := st212_p221
  have hstep := st212_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p223 : ((1051843646987/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT212 (i+1))
      = (∑ i ∈ Finset.range 222, stT212 (i+1)) + stT212 223 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 222
    simpa using h
  have hprev := st212_p222
  have hstep := st212_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p224 : ((2016156113281/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT212 (i+1))
      = (∑ i ∈ Finset.range 223, stT212 (i+1)) + stT212 224 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 223
    simpa using h
  have hprev := st212_p223
  have hstep := st212_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p225 : ((1039974191411/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT212 (i+1))
      = (∑ i ∈ Finset.range 224, stT212 (i+1)) + stT212 225 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 224
    simpa using h
  have hprev := st212_p224
  have hstep := st212_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p226 : ((4483112254049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT212 (i+1))
      = (∑ i ∈ Finset.range 225, stT212 (i+1)) + stT212 226 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 225
    simpa using h
  have hprev := st212_p225
  have hstep := st212_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p227 : ((947462570653/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT212 (i+1))
      = (∑ i ∈ Finset.range 226, stT212 (i+1)) + stT212 227 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 226
    simpa using h
  have hprev := st212_p226
  have hstep := st212_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p228 : ((1887079264157/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT212 (i+1))
      = (∑ i ∈ Finset.range 227, stT212 (i+1)) + stT212 228 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 227
    simpa using h
  have hprev := st212_p227
  have hstep := st212_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p229 : ((222099645463/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT212 (i+1))
      = (∑ i ∈ Finset.range 228, stT212 (i+1)) + stT212 229 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 228
    simpa using h
  have hprev := st212_p228
  have hstep := st212_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p230 : ((1032788857703/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT212 (i+1))
      = (∑ i ∈ Finset.range 229, stT212 (i+1)) + stT212 230 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 229
    simpa using h
  have hprev := st212_p229
  have hstep := st212_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p231 : ((1007610268323/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT212 (i+1))
      = (∑ i ∈ Finset.range 230, stT212 (i+1)) + stT212 231 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 230
    simpa using h
  have hprev := st212_p230
  have hstep := st212_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p232 : ((21085199709/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT212 (i+1))
      = (∑ i ∈ Finset.range 231, stT212 (i+1)) + stT212 232 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 231
    simpa using h
  have hprev := st212_p231
  have hstep := st212_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p233 : ((2272050619799/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT212 (i+1))
      = (∑ i ∈ Finset.range 232, stT212 (i+1)) + stT212 233 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 232
    simpa using h
  have hprev := st212_p232
  have hstep := st212_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p234 : ((2379456325509/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT212 (i+1))
      = (∑ i ∈ Finset.range 233, stT212 (i+1)) + stT212 234 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 233
    simpa using h
  have hprev := st212_p233
  have hstep := st212_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p235 : ((9396585391083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT212 (i+1))
      = (∑ i ∈ Finset.range 234, stT212 (i+1)) + stT212 235 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 234
    simpa using h
  have hprev := st212_p234
  have hstep := st212_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p236 : ((8820280348563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT212 (i+1))
      = (∑ i ∈ Finset.range 235, stT212 (i+1)) + stT212 236 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 235
    simpa using h
  have hprev := st212_p235
  have hstep := st212_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p237 : ((8225217715973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT212 (i+1))
      = (∑ i ∈ Finset.range 236, stT212 (i+1)) + stT212 237 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 236
    simpa using h
  have hprev := st212_p236
  have hstep := st212_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p238 : ((1611025537993/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT212 (i+1))
      = (∑ i ∈ Finset.range 237, stT212 (i+1)) + stT212 238 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 237
    simpa using h
  have hprev := st212_p237
  have hstep := st212_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p239 : ((8432742154153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT212 (i+1))
      = (∑ i ∈ Finset.range 238, stT212 (i+1)) + stT212 239 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 238
    simpa using h
  have hprev := st212_p238
  have hstep := st212_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p240 : ((9076959779099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT212 (i+1))
      = (∑ i ∈ Finset.range 239, stT212 (i+1)) + stT212 240 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 239
    simpa using h
  have hprev := st212_p239
  have hstep := st212_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p241 : ((9516704467307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT212 (i+1))
      = (∑ i ∈ Finset.range 240, stT212 (i+1)) + stT212 241 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 240
    simpa using h
  have hprev := st212_p240
  have hstep := st212_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p242 : ((9435651948707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT212 (i+1))
      = (∑ i ∈ Finset.range 241, stT212 (i+1)) + stT212 242 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 241
    simpa using h
  have hprev := st212_p241
  have hstep := st212_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p243 : ((8895608180863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT212 (i+1))
      = (∑ i ∈ Finset.range 242, stT212 (i+1)) + stT212 243 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 242
    simpa using h
  have hprev := st212_p242
  have hstep := st212_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p244 : ((64719283271/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT212 (i+1))
      = (∑ i ∈ Finset.range 243, stT212 (i+1)) + stT212 244 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 243
    simpa using h
  have hprev := st212_p243
  have hstep := st212_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p245 : ((4016657712479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT212 (i+1))
      = (∑ i ∈ Finset.range 244, stT212 (i+1)) + stT212 245 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 244
    simpa using h
  have hprev := st212_p244
  have hstep := st212_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p246 : ((831648651687/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT212 (i+1))
      = (∑ i ∈ Finset.range 245, stT212 (i+1)) + stT212 246 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 245
    simpa using h
  have hprev := st212_p245
  have hstep := st212_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p247 : ((4466440775799/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT212 (i+1))
      = (∑ i ∈ Finset.range 246, stT212 (i+1)) + stT212 247 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 246
    simpa using h
  have hprev := st212_p246
  have hstep := st212_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p248 : ((4727374658299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT212 (i+1))
      = (∑ i ∈ Finset.range 247, stT212 (i+1)) + stT212 248 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 247
    simpa using h
  have hprev := st212_p247
  have hstep := st212_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p249 : ((4762650587897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT212 (i+1))
      = (∑ i ∈ Finset.range 248, stT212 (i+1)) + stT212 249 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 248
    simpa using h
  have hprev := st212_p248
  have hstep := st212_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p250 : ((909969686761/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT212 (i+1))
      = (∑ i ∈ Finset.range 249, stT212 (i+1)) + stT212 250 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 249
    simpa using h
  have hprev := st212_p249
  have hstep := st212_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p251 : ((1693705801799/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT212 (i+1))
      = (∑ i ∈ Finset.range 250, stT212 (i+1)) + stT212 251 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 250
    simpa using h
  have hprev := st212_p250
  have hstep := st212_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p252 : ((1611170931979/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT212 (i+1))
      = (∑ i ∈ Finset.range 251, stT212 (i+1)) + stT212 252 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 251
    simpa using h
  have hprev := st212_p251
  have hstep := st212_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p253 : ((8134427578627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT212 (i+1))
      = (∑ i ∈ Finset.range 252, stT212 (i+1)) + stT212 253 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 252
    simpa using h
  have hprev := st212_p252
  have hstep := st212_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p254 : ((4324498261061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT212 (i+1))
      = (∑ i ∈ Finset.range 253, stT212 (i+1)) + stT212 254 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 253
    simpa using h
  have hprev := st212_p253
  have hstep := st212_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p255 : ((4629781208613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT212 (i+1))
      = (∑ i ∈ Finset.range 254, stT212 (i+1)) + stT212 255 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 254
    simpa using h
  have hprev := st212_p254
  have hstep := st212_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p256 : ((4784275271113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT212 (i+1))
      = (∑ i ∈ Finset.range 255, stT212 (i+1)) + stT212 256 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 255
    simpa using h
  have hprev := st212_p255
  have hstep := st212_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p257 : ((4689315537457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT212 (i+1))
      = (∑ i ∈ Finset.range 256, stT212 (i+1)) + stT212 257 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 256
    simpa using h
  have hprev := st212_p256
  have hstep := st212_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p258 : ((8814842040147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT212 (i+1))
      = (∑ i ∈ Finset.range 257, stT212 (i+1)) + stT212 258 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 257
    simpa using h
  have hprev := st212_p257
  have hstep := st212_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p259 : ((8238217515217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT212 (i+1))
      = (∑ i ∈ Finset.range 258, stT212 (i+1)) + stT212 259 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 258
    simpa using h
  have hprev := st212_p258
  have hstep := st212_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p260 : ((8012833880137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT212 (i+1))
      = (∑ i ∈ Finset.range 259, stT212 (i+1)) + stT212 260 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 259
    simpa using h
  have hprev := st212_p259
  have hstep := st212_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p261 : ((1655508106157/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT212 (i+1))
      = (∑ i ∈ Finset.range 260, stT212 (i+1)) + stT212 261 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 260
    simpa using h
  have hprev := st212_p260
  have hstep := st212_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p262 : ((8864309100721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT212 (i+1))
      = (∑ i ∈ Finset.range 261, stT212 (i+1)) + stT212 262 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 261
    simpa using h
  have hprev := st212_p261
  have hstep := st212_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p263 : ((9408501277753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT212 (i+1))
      = (∑ i ∈ Finset.range 262, stT212 (i+1)) + stT212 263 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 262
    simpa using h
  have hprev := st212_p262
  have hstep := st212_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p264 : ((2394160263217/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT212 (i+1))
      = (∑ i ∈ Finset.range 263, stT212 (i+1)) + stT212 264 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 263
    simpa using h
  have hprev := st212_p263
  have hstep := st212_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p265 : ((2317213392683/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT212 (i+1))
      = (∑ i ∈ Finset.range 264, stT212 (i+1)) + stT212 265 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 264
    simpa using h
  have hprev := st212_p264
  have hstep := st212_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p266 : ((2168593774943/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT212 (i+1))
      = (∑ i ∈ Finset.range 265, stT212 (i+1)) + stT212 266 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 265
    simpa using h
  have hprev := st212_p265
  have hstep := st212_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p267 : ((8151947146649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT212 (i+1))
      = (∑ i ∈ Finset.range 266, stT212 (i+1)) + stT212 267 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 266
    simpa using h
  have hprev := st212_p266
  have hstep := st212_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p268 : ((320498082593/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT212 (i+1))
      = (∑ i ∈ Finset.range 267, stT212 (i+1)) + stT212 268 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 267
    simpa using h
  have hprev := st212_p267
  have hstep := st212_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p269 : ((1667178449009/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT212 (i+1))
      = (∑ i ∈ Finset.range 268, stT212 (i+1)) + stT212 269 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 268
    simpa using h
  have hprev := st212_p268
  have hstep := st212_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p270 : ((1785822580601/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT212 (i+1))
      = (∑ i ∈ Finset.range 269, stT212 (i+1)) + stT212 270 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 269
    simpa using h
  have hprev := st212_p269
  have hstep := st212_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p271 : ((1888826464697/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT212 (i+1))
      = (∑ i ∈ Finset.range 270, stT212 (i+1)) + stT212 271 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 270
    simpa using h
  have hprev := st212_p270
  have hstep := st212_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p272 : ((1197875495459/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT212 (i+1))
      = (∑ i ∈ Finset.range 271, stT212 (i+1)) + stT212 272 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 271
    simpa using h
  have hprev := st212_p271
  have hstep := st212_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p273 : ((2317065147331/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT212 (i+1))
      = (∑ i ∈ Finset.range 272, stT212 (i+1)) + stT212 273 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 272
    simpa using h
  have hprev := st212_p272
  have hstep := st212_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p274 : ((8682708934467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT212 (i+1))
      = (∑ i ∈ Finset.range 273, stT212 (i+1)) + stT212 274 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 273
    simpa using h
  have hprev := st212_p273
  have hstep := st212_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p275 : ((4080207216273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT212 (i+1))
      = (∑ i ∈ Finset.range 274, stT212 (i+1)) + stT212 275 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 274
    simpa using h
  have hprev := st212_p274
  have hstep := st212_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p276 : ((3997660341863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT212 (i+1))
      = (∑ i ∈ Finset.range 275, stT212 (i+1)) + stT212 276 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 275
    simpa using h
  have hprev := st212_p275
  have hstep := st212_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p277 : ((4138754632211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT212 (i+1))
      = (∑ i ∈ Finset.range 276, stT212 (i+1)) + stT212 277 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 276
    simpa using h
  have hprev := st212_p276
  have hstep := st212_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p278 : ((4423596249971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT212 (i+1))
      = (∑ i ∈ Finset.range 277, stT212 (i+1)) + stT212 278 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 277
    simpa using h
  have hprev := st212_p277
  have hstep := st212_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p279 : ((4693985293047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT212 (i+1))
      = (∑ i ∈ Finset.range 278, stT212 (i+1)) + stT212 279 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 278
    simpa using h
  have hprev := st212_p278
  have hstep := st212_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p280 : ((4801730913949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT212 (i+1))
      = (∑ i ∈ Finset.range 279, stT212 (i+1)) + stT212 280 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 279
    simpa using h
  have hprev := st212_p279
  have hstep := st212_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p281 : ((2344595132537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT212 (i+1))
      = (∑ i ∈ Finset.range 280, stT212 (i+1)) + stT212 281 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 280
    simpa using h
  have hprev := st212_p280
  have hstep := st212_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p282 : ((2209320490103/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT212 (i+1))
      = (∑ i ∈ Finset.range 281, stT212 (i+1)) + stT212 282 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 281
    simpa using h
  have hprev := st212_p281
  have hstep := st212_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p283 : ((8272911468349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT212 (i+1))
      = (∑ i ∈ Finset.range 282, stT212 (i+1)) + stT212 283 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 282
    simpa using h
  have hprev := st212_p282
  have hstep := st212_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p284 : ((1996655566579/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT212 (i+1))
      = (∑ i ∈ Finset.range 283, stT212 (i+1)) + stT212 284 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 283
    simpa using h
  have hprev := st212_p283
  have hstep := st212_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p285 : ((2032100782377/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT212 (i+1))
      = (∑ i ∈ Finset.range 284, stT212 (i+1)) + stT212 285 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 284
    simpa using h
  have hprev := st212_p284
  have hstep := st212_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p286 : ((2155219036521/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT212 (i+1))
      = (∑ i ∈ Finset.range 285, stT212 (i+1)) + stT212 286 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 285
    simpa using h
  have hprev := st212_p285
  have hstep := st212_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p287 : ((9204187698317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT212 (i+1))
      = (∑ i ∈ Finset.range 286, stT212 (i+1)) + stT212 287 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 286
    simpa using h
  have hprev := st212_p286
  have hstep := st212_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p288 : ((1196830434749/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT212 (i+1))
      = (∑ i ∈ Finset.range 287, stT212 (i+1)) + stT212 288 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 287
    simpa using h
  have hprev := st212_p287
  have hstep := st212_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p289 : ((2385582771569/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT212 (i+1))
      = (∑ i ∈ Finset.range 288, stT212 (i+1)) + stT212 289 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 288
    simpa using h
  have hprev := st212_p288
  have hstep := st212_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p290 : ((1140789736519/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT212 (i+1))
      = (∑ i ∈ Finset.range 289, stT212 (i+1)) + stT212 290 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 289
    simpa using h
  have hprev := st212_p289
  have hstep := st212_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p291 : ((8540925828919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT212 (i+1))
      = (∑ i ∈ Finset.range 290, stT212 (i+1)) + stT212 291 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 290
    simpa using h
  have hprev := st212_p290
  have hstep := st212_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p292 : ((8083466787483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT212 (i+1))
      = (∑ i ∈ Finset.range 291, stT212 (i+1)) + stT212 292 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 291
    simpa using h
  have hprev := st212_p291
  have hstep := st212_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p293 : ((3991571335997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT212 (i+1))
      = (∑ i ∈ Finset.range 292, stT212 (i+1)) + stT212 293 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 292
    simpa using h
  have hprev := st212_p292
  have hstep := st212_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p294 : ((4143918879839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT212 (i+1))
      = (∑ i ∈ Finset.range 293, stT212 (i+1)) + stT212 294 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 293
    simpa using h
  have hprev := st212_p293
  have hstep := st212_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p295 : ((4421913582623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT212 (i+1))
      = (∑ i ∈ Finset.range 294, stT212 (i+1)) + stT212 295 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 294
    simpa using h
  have hprev := st212_p294
  have hstep := st212_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p296 : ((4687699770311/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT212 (i+1))
      = (∑ i ∈ Finset.range 295, stT212 (i+1)) + stT212 296 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 295
    simpa using h
  have hprev := st212_p295
  have hstep := st212_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p297 : ((962226798569/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT212 (i+1))
      = (∑ i ∈ Finset.range 296, stT212 (i+1)) + stT212 297 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 296
    simpa using h
  have hprev := st212_p296
  have hstep := st212_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p298 : ((47330017699/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT212 (i+1))
      = (∑ i ∈ Finset.range 297, stT212 (i+1)) + stT212 298 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 297
    simpa using h
  have hprev := st212_p297
  have hstep := st212_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p299 : ((359384912341/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT212 (i+1))
      = (∑ i ∈ Finset.range 298, stT212 (i+1)) + stT212 299 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 298
    simpa using h
  have hprev := st212_p298
  have hstep := st212_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p300 : ((8411419498109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT212 (i+1))
      = (∑ i ∈ Finset.range 299, stT212 (i+1)) + stT212 300 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 299
    simpa using h
  have hprev := st212_p299
  have hstep := st212_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p301 : ((8020636775147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT212 (i+1))
      = (∑ i ∈ Finset.range 300, stT212 (i+1)) + stT212 301 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 300
    simpa using h
  have hprev := st212_p300
  have hstep := st212_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p302 : ((1599314178151/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT212 (i+1))
      = (∑ i ∈ Finset.range 301, stT212 (i+1)) + stT212 302 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 301
    simpa using h
  have hprev := st212_p301
  have hstep := st212_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p303 : ((8348334337763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT212 (i+1))
      = (∑ i ∈ Finset.range 302, stT212 (i+1)) + stT212 303 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 302
    simpa using h
  have hprev := st212_p302
  have hstep := st212_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p304 : ((8908855149541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT212 (i+1))
      = (∑ i ∈ Finset.range 303, stT212 (i+1)) + stT212 304 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 303
    simpa using h
  have hprev := st212_p303
  have hstep := st212_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p305 : ((9415929042607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT212 (i+1))
      = (∑ i ∈ Finset.range 304, stT212 (i+1)) + stT212 305 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 304
    simpa using h
  have hprev := st212_p304
  have hstep := st212_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p306 : ((9635278798273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT212 (i+1))
      = (∑ i ∈ Finset.range 305, stT212 (i+1)) + stT212 306 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 305
    simpa using h
  have hprev := st212_p305
  have hstep := st212_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p307 : ((2366945308781/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT212 (i+1))
      = (∑ i ∈ Finset.range 306, stT212 (i+1)) + stT212 307 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 306
    simpa using h
  have hprev := st212_p306
  have hstep := st212_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p308 : ((281007772583/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT212 (i+1))
      = (∑ i ∈ Finset.range 307, stT212 (i+1)) + stT212 308 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 307
    simpa using h
  have hprev := st212_p307
  have hstep := st212_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p309 : ((2106597973513/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT212 (i+1))
      = (∑ i ∈ Finset.range 308, stT212 (i+1)) + stT212 309 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 308
    simpa using h
  have hprev := st212_p308
  have hstep := st212_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p310 : ((4013022567803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT212 (i+1))
      = (∑ i ∈ Finset.range 309, stT212 (i+1)) + stT212 310 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 309
    simpa using h
  have hprev := st212_p309
  have hstep := st212_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p311 : ((3984872887463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT212 (i+1))
      = (∑ i ∈ Finset.range 310, stT212 (i+1)) + stT212 311 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 310
    simpa using h
  have hprev := st212_p310
  have hstep := st212_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p312 : ((2070131382903/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT212 (i+1))
      = (∑ i ∈ Finset.range 311, stT212 (i+1)) + stT212 312 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 311
    simpa using h
  have hprev := st212_p311
  have hstep := st212_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p313 : ((8818574780943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT212 (i+1))
      = (∑ i ∈ Finset.range 312, stT212 (i+1)) + stT212 313 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 312
    simpa using h
  have hprev := st212_p312
  have hstep := st212_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p314 : ((9345701500847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT212 (i+1))
      = (∑ i ∈ Finset.range 313, stT212 (i+1)) + stT212 314 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 313
    simpa using h
  have hprev := st212_p313
  have hstep := st212_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p315 : ((9631332563867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT212 (i+1))
      = (∑ i ∈ Finset.range 314, stT212 (i+1)) + stT212 315 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 314
    simpa using h
  have hprev := st212_p314
  have hstep := st212_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p316 : ((9552660222923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT212 (i+1))
      = (∑ i ∈ Finset.range 315, stT212 (i+1)) + stT212 316 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 315
    simpa using h
  have hprev := st212_p315
  have hstep := st212_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p317 : ((1829160671279/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT212 (i+1))
      = (∑ i ∈ Finset.range 316, stT212 (i+1)) + stT212 317 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 316
    simpa using h
  have hprev := st212_p316
  have hstep := st212_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p318 : ((8587425978651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT212 (i+1))
      = (∑ i ∈ Finset.range 317, stT212 (i+1)) + stT212 318 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 317
    simpa using h
  have hprev := st212_p317
  have hstep := st212_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p319 : ((8116820235147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT212 (i+1))
      = (∑ i ∈ Finset.range 318, stT212 (i+1)) + stT212 319 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 318
    simpa using h
  have hprev := st212_p318
  have hstep := st212_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p320 : ((1983297604467/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT212 (i+1))
      = (∑ i ∈ Finset.range 319, stT212 (i+1)) + stT212 320 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 319
    simpa using h
  have hprev := st212_p319
  have hstep := st212_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p321 : ((8112353288433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT212 (i+1))
      = (∑ i ∈ Finset.range 320, stT212 (i+1)) + stT212 321 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 320
    simpa using h
  have hprev := st212_p320
  have hstep := st212_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p322 : ((8577071313579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT212 (i+1))
      = (∑ i ∈ Finset.range 321, stT212 (i+1)) + stT212 322 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 321
    simpa using h
  have hprev := st212_p321
  have hstep := st212_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p323 : ((9131982995779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT212 (i+1))
      = (∑ i ∈ Finset.range 322, stT212 (i+1)) + stT212 323 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 322
    simpa using h
  have hprev := st212_p322
  have hstep := st212_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p324 : ((1193328308753/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT212 (i+1))
      = (∑ i ∈ Finset.range 323, stT212 (i+1)) + stT212 324 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 323
    simpa using h
  have hprev := st212_p323
  have hstep := st212_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p325 : ((2412751230931/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT212 (i+1))
      = (∑ i ∈ Finset.range 324, stT212 (i+1)) + stT212 325 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 324
    simpa using h
  have hprev := st212_p324
  have hstep := st212_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p326 : ((4702063365987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT212 (i+1))
      = (∑ i ∈ Finset.range 325, stT212 (i+1)) + stT212 326 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 325
    simpa using h
  have hprev := st212_p325
  have hstep := st212_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p327 : ((2227115962587/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT212 (i+1))
      = (∑ i ∈ Finset.range 326, stT212 (i+1)) + stT212 327 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 326
    simpa using h
  have hprev := st212_p326
  have hstep := st212_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p328 : ((4182993970439/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT212 (i+1))
      = (∑ i ∈ Finset.range 327, stT212 (i+1)) + stT212 328 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 327
    simpa using h
  have hprev := st212_p327
  have hstep := st212_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p329 : ((1998794655303/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT212 (i+1))
      = (∑ i ∈ Finset.range 328, stT212 (i+1)) + stT212 329 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 328
    simpa using h
  have hprev := st212_p328
  have hstep := st212_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p330 : ((1985838510951/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT212 (i+1))
      = (∑ i ∈ Finset.range 329, stT212 (i+1)) + stT212 330 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 329
    simpa using h
  have hprev := st212_p329
  have hstep := st212_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p331 : ((8229314982193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT212 (i+1))
      = (∑ i ∈ Finset.range 330, stT212 (i+1)) + stT212 331 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 330
    simpa using h
  have hprev := st212_p330
  have hstep := st212_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p332 : ((8738126931293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT212 (i+1))
      = (∑ i ∈ Finset.range 331, stT212 (i+1)) + stT212 332 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 331
    simpa using h
  have hprev := st212_p331
  have hstep := st212_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p333 : ((9268578291357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT212 (i+1))
      = (∑ i ∈ Finset.range 332, stT212 (i+1)) + stT212 333 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 332
    simpa using h
  have hprev := st212_p332
  have hstep := st212_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p334 : ((9613285409157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT212 (i+1))
      = (∑ i ∈ Finset.range 333, stT212 (i+1)) + stT212 334 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 333
    simpa using h
  have hprev := st212_p333
  have hstep := st212_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p335 : ((9639359251991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT212 (i+1))
      = (∑ i ∈ Finset.range 334, stT212 (i+1)) + stT212 335 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 334
    simpa using h
  have hprev := st212_p334
  have hstep := st212_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p336 : ((9338493366671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT212 (i+1))
      = (∑ i ∈ Finset.range 335, stT212 (i+1)) + stT212 336 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 335
    simpa using h
  have hprev := st212_p335
  have hstep := st212_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p337 : ((8828015661351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT212 (i+1))
      = (∑ i ∈ Finset.range 336, stT212 (i+1)) + stT212 337 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 336
    simpa using h
  have hprev := st212_p336
  have hstep := st212_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p338 : ((1037997200119/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT212 (i+1))
      = (∑ i ∈ Finset.range 337, stT212 (i+1)) + stT212 338 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 337
    simpa using h
  have hprev := st212_p337
  have hstep := st212_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p339 : ((796538905067/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT212 (i+1))
      = (∑ i ∈ Finset.range 338, stT212 (i+1)) + stT212 339 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 338
    simpa using h
  have hprev := st212_p338
  have hstep := st212_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p340 : ((7939024908219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT212 (i+1))
      = (∑ i ∈ Finset.range 339, stT212 (i+1)) + stT212 340 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 339
    simpa using h
  have hprev := st212_p339
  have hstep := st212_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p341 : ((8233054578549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT212 (i+1))
      = (∑ i ∈ Finset.range 340, stT212 (i+1)) + stT212 341 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 340
    simpa using h
  have hprev := st212_p340
  have hstep := st212_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p342 : ((8735994451611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT212 (i+1))
      = (∑ i ∈ Finset.range 341, stT212 (i+1)) + stT212 342 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 341
    simpa using h
  have hprev := st212_p341
  have hstep := st212_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p343 : ((926005329249/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT212 (i+1))
      = (∑ i ∈ Finset.range 342, stT212 (i+1)) + stT212 343 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 342
    simpa using h
  have hprev := st212_p342
  have hstep := st212_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p344 : ((4805862797109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT212 (i+1))
      = (∑ i ∈ Finset.range 343, stT212 (i+1)) + stT212 344 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 343
    simpa using h
  have hprev := st212_p343
  have hstep := st212_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p345 : ((4831445585467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT212 (i+1))
      = (∑ i ∈ Finset.range 344, stT212 (i+1)) + stT212 345 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 344
    simpa using h
  have hprev := st212_p344
  have hstep := st212_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p346 : ((4698252044051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT212 (i+1))
      = (∑ i ∈ Finset.range 345, stT212 (i+1)) + stT212 346 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 345
    simpa using h
  have hprev := st212_p345
  have hstep := st212_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p347 : ((8910918100297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT212 (i+1))
      = (∑ i ∈ Finset.range 346, stT212 (i+1)) + stT212 347 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 346
    simpa using h
  have hprev := st212_p346
  have hstep := st212_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p348 : ((8382513850029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT212 (i+1))
      = (∑ i ∈ Finset.range 347, stT212 (i+1)) + stT212 348 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 347
    simpa using h
  have hprev := st212_p347
  have hstep := st212_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p349 : ((8001117938301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT212 (i+1))
      = (∑ i ∈ Finset.range 348, stT212 (i+1)) + stT212 349 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 348
    simpa using h
  have hprev := st212_p348
  have hstep := st212_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p350 : ((7902022719331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT212 (i+1))
      = (∑ i ∈ Finset.range 349, stT212 (i+1)) + stT212 350 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 349
    simpa using h
  have hprev := st212_p349
  have hstep := st212_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p351 : ((8118881400931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT212 (i+1))
      = (∑ i ∈ Finset.range 350, stT212 (i+1)) + stT212 351 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 350
    simpa using h
  have hprev := st212_p350
  have hstep := st212_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p352 : ((2143365890701/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT212 (i+1))
      = (∑ i ∈ Finset.range 351, stT212 (i+1)) + stT212 352 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 351
    simpa using h
  have hprev := st212_p351
  have hstep := st212_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p353 : ((4552479281849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT212 (i+1))
      = (∑ i ∈ Finset.range 352, stT212 (i+1)) + stT212 353 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 352
    simpa using h
  have hprev := st212_p352
  have hstep := st212_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p354 : ((2381857464237/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT212 (i+1))
      = (∑ i ∈ Finset.range 353, stT212 (i+1)) + stT212 354 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 353
    simpa using h
  have hprev := st212_p353
  have hstep := st212_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p355 : ((2423699596279/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT212 (i+1))
      = (∑ i ∈ Finset.range 354, stT212 (i+1)) + stT212 355 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 354
    simpa using h
  have hprev := st212_p354
  have hstep := st212_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p356 : ((1193825857147/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT212 (i+1))
      = (∑ i ∈ Finset.range 355, stT212 (i+1)) + stT212 356 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 355
    simpa using h
  have hprev := st212_p355
  have hstep := st212_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p357 : ((4573002879193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT212 (i+1))
      = (∑ i ∈ Finset.range 356, stT212 (i+1)) + stT212 357 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 356
    simpa using h
  have hprev := st212_p356
  have hstep := st212_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p358 : ((8620521917449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT212 (i+1))
      = (∑ i ∈ Finset.range 357, stT212 (i+1)) + stT212 358 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 357
    simpa using h
  have hprev := st212_p357
  have hstep := st212_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p359 : ((8153263505609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT212 (i+1))
      = (∑ i ∈ Finset.range 358, stT212 (i+1)) + stT212 359 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 358
    simpa using h
  have hprev := st212_p358
  have hstep := st212_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p360 : ((7901773542713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT212 (i+1))
      = (∑ i ∈ Finset.range 359, stT212 (i+1)) + stT212 360 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 359
    simpa using h
  have hprev := st212_p359
  have hstep := st212_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p361 : ((7949415576513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT212 (i+1))
      = (∑ i ∈ Finset.range 360, stT212 (i+1)) + stT212 361 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 360
    simpa using h
  have hprev := st212_p360
  have hstep := st212_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p362 : ((8278709598213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT212 (i+1))
      = (∑ i ∈ Finset.range 361, stT212 (i+1)) + stT212 362 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 361
    simpa using h
  have hprev := st212_p361
  have hstep := st212_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p363 : ((8778716136259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT212 (i+1))
      = (∑ i ∈ Finset.range 362, stT212 (i+1)) + stT212 363 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 362
    simpa using h
  have hprev := st212_p362
  have hstep := st212_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p364 : ((9283224301081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT212 (i+1))
      = (∑ i ∈ Finset.range 363, stT212 (i+1)) + stT212 364 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 363
    simpa using h
  have hprev := st212_p363
  have hstep := st212_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p365 : ((2406569588099/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT212 (i+1))
      = (∑ i ∈ Finset.range 364, stT212 (i+1)) + stT212 365 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 364
    simpa using h
  have hprev := st212_p364
  have hstep := st212_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p366 : ((2424118986491/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT212 (i+1))
      = (∑ i ∈ Finset.range 365, stT212 (i+1)) + stT212 366 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 365
    simpa using h
  have hprev := st212_p365
  have hstep := st212_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p367 : ((473618526763/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT212 (i+1))
      = (∑ i ∈ Finset.range 366, stT212 (i+1)) + stT212 367 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 366
    simpa using h
  have hprev := st212_p366
  have hstep := st212_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p368 : ((282124949673/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT212 (i+1))
      = (∑ i ∈ Finset.range 367, stT212 (i+1)) + stT212 368 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 367
    simpa using h
  have hprev := st212_p367
  have hstep := st212_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p369 : ((132930559729/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT212 (i+1))
      = (∑ i ∈ Finset.range 368, stT212 (i+1)) + stT212 369 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 368
    simpa using h
  have hprev := st212_p368
  have hstep := st212_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p370 : ((126220520197/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT212 (i+1))
      = (∑ i ∈ Finset.range 369, stT212 (i+1)) + stT212 370 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 369
    simpa using h
  have hprev := st212_p369
  have hstep := st212_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p371 : ((7876015597883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT212 (i+1))
      = (∑ i ∈ Finset.range 370, stT212 (i+1)) + stT212 371 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 370
    simpa using h
  have hprev := st212_p370
  have hstep := st212_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p372 : ((7964156347883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT212 (i+1))
      = (∑ i ∈ Finset.range 371, stT212 (i+1)) + stT212 372 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 371
    simpa using h
  have hprev := st212_p371
  have hstep := st212_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p373 : ((8313268995103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT212 (i+1))
      = (∑ i ∈ Finset.range 372, stT212 (i+1)) + stT212 373 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 372
    simpa using h
  have hprev := st212_p372
  have hstep := st212_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p374 : ((8812523732821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT212 (i+1))
      = (∑ i ∈ Finset.range 373, stT212 (i+1)) + stT212 374 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 373
    simpa using h
  have hprev := st212_p373
  have hstep := st212_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p375 : ((1861076878071/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT212 (i+1))
      = (∑ i ∈ Finset.range 374, stT212 (i+1)) + stT212 375 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 374
    simpa using h
  have hprev := st212_p374
  have hstep := st212_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p376 : ((1927778293761/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT212 (i+1))
      = (∑ i ∈ Finset.range 375, stT212 (i+1)) + stT212 376 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 375
    simpa using h
  have hprev := st212_p375
  have hstep := st212_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p377 : ((9710855021733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT212 (i+1))
      = (∑ i ∈ Finset.range 376, stT212 (i+1)) + stT212 377 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 376
    simpa using h
  have hprev := st212_p376
  have hstep := st212_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p378 : ((9500465285553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT212 (i+1))
      = (∑ i ∈ Finset.range 377, stT212 (i+1)) + stT212 378 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 377
    simpa using h
  have hprev := st212_p377
  have hstep := st212_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p379 : ((9073419296799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT212 (i+1))
      = (∑ i ∈ Finset.range 378, stT212 (i+1)) + stT212 379 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 378
    simpa using h
  have hprev := st212_p378
  have hstep := st212_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p380 : ((8560645265589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT212 (i+1))
      = (∑ i ∈ Finset.range 379, stT212 (i+1)) + stT212 380 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 379
    simpa using h
  have hprev := st212_p379
  have hstep := st212_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p381 : ((8117674822401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT212 (i+1))
      = (∑ i ∈ Finset.range 380, stT212 (i+1)) + stT212 381 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 380
    simpa using h
  have hprev := st212_p380
  have hstep := st212_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p382 : ((246171170283/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT212 (i+1))
      = (∑ i ∈ Finset.range 381, stT212 (i+1)) + stT212 382 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 381
    simpa using h
  have hprev := st212_p381
  have hstep := st212_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p383 : ((247217249931/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT212 (i+1))
      = (∑ i ∈ Finset.range 382, stT212 (i+1)) + stT212 383 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 382
    simpa using h
  have hprev := st212_p382
  have hstep := st212_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p384 : ((2051694421043/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT212 (i+1))
      = (∑ i ∈ Finset.range 383, stT212 (i+1)) + stT212 384 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 383
    simpa using h
  have hprev := st212_p383
  have hstep := st212_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p385 : ((4337983943009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT212 (i+1))
      = (∑ i ∈ Finset.range 384, stT212 (i+1)) + stT212 385 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 384
    simpa using h
  have hprev := st212_p384
  have hstep := st212_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p386 : ((917929497967/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT212 (i+1))
      = (∑ i ∈ Finset.range 385, stT212 (i+1)) + stT212 386 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 385
    simpa using h
  have hprev := st212_p385
  have hstep := st212_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p387 : ((4784450725143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT212 (i+1))
      = (∑ i ∈ Finset.range 386, stT212 (i+1)) + stT212 387 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 386
    simpa using h
  have hprev := st212_p386
  have hstep := st212_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p388 : ((1946317357231/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT212 (i+1))
      = (∑ i ∈ Finset.range 387, stT212 (i+1)) + stT212 388 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 387
    simpa using h
  have hprev := st212_p387
  have hstep := st212_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p389 : ((4810598833507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT212 (i+1))
      = (∑ i ∈ Finset.range 388, stT212 (i+1)) + stT212 389 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 388
    simpa using h
  have hprev := st212_p388
  have hstep := st212_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p390 : ((2317740321611/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT212 (i+1))
      = (∑ i ∈ Finset.range 389, stT212 (i+1)) + stT212 390 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 389
    simpa using h
  have hprev := st212_p389
  have hstep := st212_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p391 : ((1097845066357/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT212 (i+1))
      = (∑ i ∈ Finset.range 390, stT212 (i+1)) + stT212 391 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 390
    simpa using h
  have hprev := st212_p390
  have hstep := st212_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p392 : ((4148478129511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT212 (i+1))
      = (∑ i ∈ Finset.range 391, stT212 (i+1)) + stT212 392 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 391
    simpa using h
  have hprev := st212_p391
  have hstep := st212_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p393 : ((1987964582759/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT212 (i+1))
      = (∑ i ∈ Finset.range 392, stT212 (i+1)) + stT212 393 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 392
    simpa using h
  have hprev := st212_p392
  have hstep := st212_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p394 : ((392227722619/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT212 (i+1))
      = (∑ i ∈ Finset.range 393, stT212 (i+1)) + stT212 394 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 393
    simpa using h
  have hprev := st212_p393
  have hstep := st212_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p395 : ((1000517224243/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT212 (i+1))
      = (∑ i ∈ Finset.range 394, stT212 (i+1)) + stT212 395 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 394
    simpa using h
  have hprev := st212_p394
  have hstep := st212_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p396 : ((209614000013/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT212 (i+1))
      = (∑ i ∈ Finset.range 395, stT212 (i+1)) + stT212 396 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 395
    simpa using h
  have hprev := st212_p395
  have hstep := st212_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p397 : ((887855235701/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT212 (i+1))
      = (∑ i ∈ Finset.range 396, stT212 (i+1)) + stT212 397 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 396
    simpa using h
  have hprev := st212_p396
  have hstep := st212_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p398 : ((934834264343/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT212 (i+1))
      = (∑ i ∈ Finset.range 397, stT212 (i+1)) + stT212 398 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 397
    simpa using h
  have hprev := st212_p397
  have hstep := st212_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p399 : ((966417757431/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT212 (i+1))
      = (∑ i ∈ Finset.range 398, stT212 (i+1)) + stT212 399 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 398
    simpa using h
  have hprev := st212_p398
  have hstep := st212_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p400 : ((973990707431/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT212 (i+1))
      = (∑ i ∈ Finset.range 399, stT212 (i+1)) + stT212 400 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 399
    simpa using h
  have hprev := st212_p399
  have hstep := st212_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p401 : ((9555930095609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT212 (i+1))
      = (∑ i ∈ Finset.range 400, stT212 (i+1)) + stT212 401 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 400
    simpa using h
  have hprev := st212_p400
  have hstep := st212_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p402 : ((4581796476847/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT212 (i+1))
      = (∑ i ∈ Finset.range 401, stT212 (i+1)) + stT212 402 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 401
    simpa using h
  have hprev := st212_p401
  have hstep := st212_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p403 : ((173404492267/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT212 (i+1))
      = (∑ i ∈ Finset.range 402, stT212 (i+1)) + stT212 403 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 402
    simpa using h
  have hprev := st212_p402
  have hstep := st212_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p404 : ((8209394156967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT212 (i+1))
      = (∑ i ∈ Finset.range 403, stT212 (i+1)) + stT212 404 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 403
    simpa using h
  have hprev := st212_p403
  have hstep := st212_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p405 : ((7904663306831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT212 (i+1))
      = (∑ i ∈ Finset.range 404, stT212 (i+1)) + stT212 405 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 404
    simpa using h
  have hprev := st212_p404
  have hstep := st212_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p406 : ((1567341903463/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT212 (i+1))
      = (∑ i ∈ Finset.range 405, stT212 (i+1)) + stT212 406 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 405
    simpa using h
  have hprev := st212_p405
  have hstep := st212_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p407 : ((8022481833857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT212 (i+1))
      = (∑ i ∈ Finset.range 406, stT212 (i+1)) + stT212 407 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 406
    simpa using h
  have hprev := st212_p406
  have hstep := st212_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p408 : ((8411630995069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT212 (i+1))
      = (∑ i ∈ Finset.range 407, stT212 (i+1)) + stT212 408 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 407
    simpa using h
  have hprev := st212_p407
  have hstep := st212_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p409 : ((8900715721953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT212 (i+1))
      = (∑ i ∈ Finset.range 408, stT212 (i+1)) + stT212 409 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 408
    simpa using h
  have hprev := st212_p408
  have hstep := st212_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p410 : ((9361072037281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT212 (i+1))
      = (∑ i ∈ Finset.range 409, stT212 (i+1)) + stT212 410 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 409
    simpa using h
  have hprev := st212_p409
  have hstep := st212_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p411 : ((2418184449379/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT212 (i+1))
      = (∑ i ∈ Finset.range 410, stT212 (i+1)) + stT212 411 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 410
    simpa using h
  have hprev := st212_p410
  have hstep := st212_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p412 : ((2438871903403/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT212 (i+1))
      = (∑ i ∈ Finset.range 411, stT212 (i+1)) + stT212 412 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 411
    simpa using h
  have hprev := st212_p411
  have hstep := st212_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p413 : ((2397248363351/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT212 (i+1))
      = (∑ i ∈ Finset.range 412, stT212 (i+1)) + stT212 413 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 412
    simpa using h
  have hprev := st212_p412
  have hstep := st212_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p414 : ((230430252063/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT212 (i+1))
      = (∑ i ∈ Finset.range 413, stT212 (i+1)) + stT212 414 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 413
    simpa using h
  have hprev := st212_p413
  have hstep := st212_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p415 : ((546014814039/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT212 (i+1))
      = (∑ i ∈ Finset.range 414, stT212 (i+1)) + stT212 415 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 414
    simpa using h
  have hprev := st212_p414
  have hstep := st212_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p416 : ((1033637440851/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT212 (i+1))
      = (∑ i ∈ Finset.range 415, stT212 (i+1)) + stT212 416 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 415
    simpa using h
  have hprev := st212_p415
  have hstep := st212_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p417 : ((3967087497603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT212 (i+1))
      = (∑ i ∈ Finset.range 416, stT212 (i+1)) + stT212 417 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 416
    simpa using h
  have hprev := st212_p416
  have hstep := st212_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p418 : ((3907687294099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT212 (i+1))
      = (∑ i ∈ Finset.range 417, stT212 (i+1)) + stT212 418 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 417
    simpa using h
  have hprev := st212_p417
  have hstep := st212_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p419 : ((7941547978099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT212 (i+1))
      = (∑ i ∈ Finset.range 418, stT212 (i+1)) + stT212 419 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 418
    simpa using h
  have hprev := st212_p418
  have hstep := st212_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p420 : ((8280027182299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT212 (i+1))
      = (∑ i ∈ Finset.range 419, stT212 (i+1)) + stT212 420 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 419
    simpa using h
  have hprev := st212_p419
  have hstep := st212_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p421 : ((8745606869599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT212 (i+1))
      = (∑ i ∈ Finset.range 420, stT212 (i+1)) + stT212 421 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 420
    simpa using h
  have hprev := st212_p420
  have hstep := st212_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p422 : ((9222380690239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT212 (i+1))
      = (∑ i ∈ Finset.range 421, stT212 (i+1)) + stT212 422 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 421
    simpa using h
  have hprev := st212_p421
  have hstep := st212_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p423 : ((9592745517703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT212 (i+1))
      = (∑ i ∈ Finset.range 422, stT212 (i+1)) + stT212 423 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 422
    simpa using h
  have hprev := st212_p422
  have hstep := st212_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p424 : ((9766279002279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT212 (i+1))
      = (∑ i ∈ Finset.range 423, stT212 (i+1)) + stT212 424 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 423
    simpa using h
  have hprev := st212_p423
  have hstep := st212_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p425 : ((9701473868151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT212 (i+1))
      = (∑ i ∈ Finset.range 424, stT212 (i+1)) + stT212 425 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 424
    simpa using h
  have hprev := st212_p424
  have hstep := st212_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p426 : ((9415150143721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT212 (i+1))
      = (∑ i ∈ Finset.range 425, stT212 (i+1)) + stT212 426 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 425
    simpa using h
  have hprev := st212_p425
  have hstep := st212_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p427 : ((8977601217621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT212 (i+1))
      = (∑ i ∈ Finset.range 426, stT212 (i+1)) + stT212 427 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 426
    simpa using h
  have hprev := st212_p426
  have hstep := st212_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p428 : ((265466312037/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT212 (i+1))
      = (∑ i ∈ Finset.range 427, stT212 (i+1)) + stT212 428 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 427
    simpa using h
  have hprev := st212_p427
  have hstep := st212_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p429 : ((4041537418017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT212 (i+1))
      = (∑ i ∈ Finset.range 428, stT212 (i+1)) + stT212 429 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 428
    simpa using h
  have hprev := st212_p428
  have hstep := st212_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p430 : ((7840064390203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT212 (i+1))
      = (∑ i ∈ Finset.range 429, stT212 (i+1)) + stT212 430 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 429
    simpa using h
  have hprev := st212_p429
  have hstep := st212_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p431 : ((7822878386767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT212 (i+1))
      = (∑ i ∈ Finset.range 430, stT212 (i+1)) + stT212 431 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 430
    simpa using h
  have hprev := st212_p430
  have hstep := st212_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p432 : ((8034582047017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT212 (i+1))
      = (∑ i ∈ Finset.range 431, stT212 (i+1)) + stT212 432 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 431
    simpa using h
  have hprev := st212_p431
  have hstep := st212_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p433 : ((1053037494767/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT212 (i+1))
      = (∑ i ∈ Finset.range 432, stT212 (i+1)) + stT212 433 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 432
    simpa using h
  have hprev := st212_p432
  have hstep := st212_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p434 : ((8899865699101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT212 (i+1))
      = (∑ i ∈ Finset.range 433, stT212 (i+1)) + stT212 434 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 433
    simpa using h
  have hprev := st212_p433
  have hstep := st212_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p435 : ((4674951308201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT212 (i+1))
      = (∑ i ∈ Finset.range 434, stT212 (i+1)) + stT212 435 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 434
    simpa using h
  have hprev := st212_p434
  have hstep := st212_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p436 : ((9669956821911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT212 (i+1))
      = (∑ i ∈ Finset.range 435, stT212 (i+1)) + stT212 436 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 435
    simpa using h
  have hprev := st212_p435
  have hstep := st212_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p437 : ((9786570006011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT212 (i+1))
      = (∑ i ∈ Finset.range 436, stT212 (i+1)) + stT212 437 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 436
    simpa using h
  have hprev := st212_p436
  have hstep := st212_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p438 : ((1934752917043/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT212 (i+1))
      = (∑ i ∈ Finset.range 437, stT212 (i+1)) + stT212 438 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 437
    simpa using h
  have hprev := st212_p437
  have hstep := st212_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p439 : ((9358406744263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT212 (i+1))
      = (∑ i ∈ Finset.range 438, stT212 (i+1)) + stT212 439 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 438
    simpa using h
  have hprev := st212_p438
  have hstep := st212_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p440 : ((8913343574291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT212 (i+1))
      = (∑ i ∈ Finset.range 439, stT212 (i+1)) + stT212 440 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 439
    simpa using h
  have hprev := st212_p439
  have hstep := st212_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p441 : ((1055031393641/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT212 (i+1))
      = (∑ i ∈ Finset.range 440, stT212 (i+1)) + stT212 441 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 440
    simpa using h
  have hprev := st212_p440
  have hstep := st212_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p442 : ((2011562987427/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT212 (i+1))
      = (∑ i ∈ Finset.range 441, stT212 (i+1)) + stT212 442 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 441
    simpa using h
  have hprev := st212_p441
  have hstep := st212_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p443 : ((7819722343973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT212 (i+1))
      = (∑ i ∈ Finset.range 442, stT212 (i+1)) + stT212 443 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 442
    simpa using h
  have hprev := st212_p442
  have hstep := st212_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p444 : ((1562143726237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT212 (i+1))
      = (∑ i ∈ Finset.range 443, stT212 (i+1)) + stT212 444 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 443
    simpa using h
  have hprev := st212_p443
  have hstep := st212_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p445 : ((160406039689/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT212 (i+1))
      = (∑ i ∈ Finset.range 444, stT212 (i+1)) + stT212 445 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 444
    simpa using h
  have hprev := st212_p444
  have hstep := st212_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p446 : ((8400953876507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT212 (i+1))
      = (∑ i ∈ Finset.range 445, stT212 (i+1)) + stT212 446 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 445
    simpa using h
  have hprev := st212_p445
  have hstep := st212_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p447 : ((2216927986811/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT212 (i+1))
      = (∑ i ∈ Finset.range 446, stT212 (i+1)) + stT212 447 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 446
    simpa using h
  have hprev := st212_p446
  have hstep := st212_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p448 : ((9317385639599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT212 (i+1))
      = (∑ i ∈ Finset.range 447, stT212 (i+1)) + stT212 448 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 447
    simpa using h
  have hprev := st212_p447
  have hstep := st212_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p449 : ((193028519049/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT212 (i+1))
      = (∑ i ∈ Finset.range 448, stT212 (i+1)) + stT212 449 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 448
    simpa using h
  have hprev := st212_p448
  have hstep := st212_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p450 : ((4898689615253/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT212 (i+1))
      = (∑ i ∈ Finset.range 449, stT212 (i+1)) + stT212 450 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 449
    simpa using h
  have hprev := st212_p449
  have hstep := st212_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p451 : ((2431077058157/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT212 (i+1))
      = (∑ i ∈ Finset.range 450, stT212 (i+1)) + stT212 451 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 450
    simpa using h
  have hprev := st212_p450
  have hstep := st212_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p452 : ((9448965017921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT212 (i+1))
      = (∑ i ∈ Finset.range 451, stT212 (i+1)) + stT212 452 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 451
    simpa using h
  have hprev := st212_p451
  have hstep := st212_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p453 : ((4515770914543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT212 (i+1))
      = (∑ i ∈ Finset.range 452, stT212 (i+1)) + stT212 453 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 452
    simpa using h
  have hprev := st212_p452
  have hstep := st212_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p454 : ((4281107741233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT212 (i+1))
      = (∑ i ∈ Finset.range 453, stT212 (i+1)) + stT212 454 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 453
    simpa using h
  have hprev := st212_p453
  have hstep := st212_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p455 : ((4070740465009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT212 (i+1))
      = (∑ i ∈ Finset.range 454, stT212 (i+1)) + stT212 455 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 454
    simpa using h
  have hprev := st212_p454
  have hstep := st212_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p456 : ((7858638982413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT212 (i+1))
      = (∑ i ∈ Finset.range 455, stT212 (i+1)) + stT212 456 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 455
    simpa using h
  have hprev := st212_p455
  have hstep := st212_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p457 : ((7773008863677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT212 (i+1))
      = (∑ i ∈ Finset.range 456, stT212 (i+1)) + stT212 457 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 456
    simpa using h
  have hprev := st212_p456
  have hstep := st212_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p458 : ((7901824647059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT212 (i+1))
      = (∑ i ∈ Finset.range 457, stT212 (i+1)) + stT212 458 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 457
    simpa using h
  have hprev := st212_p457
  have hstep := st212_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p459 : ((8217131295779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT212 (i+1))
      = (∑ i ∈ Finset.range 458, stT212 (i+1)) + stT212 459 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 458
    simpa using h
  have hprev := st212_p458
  have hstep := st212_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p460 : ((8652193834491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT212 (i+1))
      = (∑ i ∈ Finset.range 459, stT212 (i+1)) + stT212 460 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 459
    simpa using h
  have hprev := st212_p459
  have hstep := st212_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p461 : ((1823183606221/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT212 (i+1))
      = (∑ i ∈ Finset.range 460, stT212 (i+1)) + stT212 461 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 460
    simpa using h
  have hprev := st212_p460
  have hstep := st212_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p462 : ((9512028326599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT212 (i+1))
      = (∑ i ∈ Finset.range 461, stT212 (i+1)) + stT212 462 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 461
    simpa using h
  have hprev := st212_p461
  have hstep := st212_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p463 : ((1219876791611/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT212 (i+1))
      = (∑ i ∈ Finset.range 462, stT212 (i+1)) + stT212 463 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 462
    simpa using h
  have hprev := st212_p462
  have hstep := st212_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p464 : ((196134286463/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT212 (i+1))
      = (∑ i ∈ Finset.range 463, stT212 (i+1)) + stT212 464 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 463
    simpa using h
  have hprev := st212_p463
  have hstep := st212_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p465 : ((9646181329781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT212 (i+1))
      = (∑ i ∈ Finset.range 464, stT212 (i+1)) + stT212 465 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 464
    simpa using h
  have hprev := st212_p464
  have hstep := st212_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p466 : ((9311004896891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT212 (i+1))
      = (∑ i ∈ Finset.range 465, stT212 (i+1)) + stT212 466 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 465
    simpa using h
  have hprev := st212_p465
  have hstep := st212_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p467 : ((2217485684839/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT212 (i+1))
      = (∑ i ∈ Finset.range 466, stT212 (i+1)) + stT212 467 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 466
    simpa using h
  have hprev := st212_p466
  have hstep := st212_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p468 : ((420629210197/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT212 (i+1))
      = (∑ i ∈ Finset.range 467, stT212 (i+1)) + stT212 468 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 467
    simpa using h
  have hprev := st212_p467
  have hstep := st212_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p469 : ((4015529944373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT212 (i+1))
      = (∑ i ∈ Finset.range 468, stT212 (i+1)) + stT212 469 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 468
    simpa using h
  have hprev := st212_p468
  have hstep := st212_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p470 : ((3900766041041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT212 (i+1))
      = (∑ i ∈ Finset.range 469, stT212 (i+1)) + stT212 470 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 469
    simpa using h
  have hprev := st212_p469
  have hstep := st212_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p471 : ((3884596489649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT212 (i+1))
      = (∑ i ∈ Finset.range 470, stT212 (i+1)) + stT212 471 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 470
    simpa using h
  have hprev := st212_p470
  have hstep := st212_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p472 : ((7939659809461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT212 (i+1))
      = (∑ i ∈ Finset.range 471, stT212 (i+1)) + stT212 472 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 471
    simpa using h
  have hprev := st212_p471
  have hstep := st212_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p473 : ((8278352167861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT212 (i+1))
      = (∑ i ∈ Finset.range 472, stT212 (i+1)) + stT212 473 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 472
    simpa using h
  have hprev := st212_p472
  have hstep := st212_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p474 : ((4358905719863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT212 (i+1))
      = (∑ i ∈ Finset.range 473, stT212 (i+1)) + stT212 474 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 473
    simpa using h
  have hprev := st212_p473
  have hstep := st212_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p475 : ((2292834817757/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT212 (i+1))
      = (∑ i ∈ Finset.range 474, stT212 (i+1)) + stT212 475 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 474
    simpa using h
  have hprev := st212_p474
  have hstep := st212_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p476 : ((59688781589/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT212 (i+1))
      = (∑ i ∈ Finset.range 475, stT212 (i+1)) + stT212 476 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 475
    simpa using h
  have hprev := st212_p475
  have hstep := st212_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p477 : ((2445234962271/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT212 (i+1))
      = (∑ i ∈ Finset.range 476, stT212 (i+1)) + stT212 477 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 476
    simpa using h
  have hprev := st212_p476
  have hstep := st212_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p478 : ((9819389340591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT212 (i+1))
      = (∑ i ∈ Finset.range 477, stT212 (i+1)) + stT212 478 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 477
    simpa using h
  have hprev := st212_p477
  have hstep := st212_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p479 : ((9658910423391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT212 (i+1))
      = (∑ i ∈ Finset.range 478, stT212 (i+1)) + stT212 479 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 478
    simpa using h
  have hprev := st212_p478
  have hstep := st212_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p480 : ((9331151491203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT212 (i+1))
      = (∑ i ∈ Finset.range 479, stT212 (i+1)) + stT212 480 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 479
    simpa using h
  have hprev := st212_p479
  have hstep := st212_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p481 : ((2224892111517/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT212 (i+1))
      = (∑ i ∈ Finset.range 480, stT212 (i+1)) + stT212 481 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 480
    simpa using h
  have hprev := st212_p480
  have hstep := st212_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p482 : ((422344745321/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT212 (i+1))
      = (∑ i ∈ Finset.range 481, stT212 (i+1)) + stT212 482 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 481
    simpa using h
  have hprev := st212_p481
  have hstep := st212_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p483 : ((2014802019739/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT212 (i+1))
      = (∑ i ∈ Finset.range 482, stT212 (i+1)) + stT212 483 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 482
    simpa using h
  have hprev := st212_p482
  have hstep := st212_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p484 : ((1952399672129/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT212 (i+1))
      = (∑ i ∈ Finset.range 483, stT212 (i+1)) + stT212 484 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 483
    simpa using h
  have hprev := st212_p483
  have hstep := st212_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p485 : ((309781486949/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT212 (i+1))
      = (∑ i ∈ Finset.range 484, stT212 (i+1)) + stT212 485 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 484
    simpa using h
  have hprev := st212_p484
  have hstep := st212_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p486 : ((7875506793077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT212 (i+1))
      = (∑ i ∈ Finset.range 485, stT212 (i+1)) + stT212 486 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 485
    simpa using h
  have hprev := st212_p485
  have hstep := st212_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p487 : ((8177237497343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT212 (i+1))
      = (∑ i ∈ Finset.range 486, stT212 (i+1)) + stT212 487 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 486
    simpa using h
  have hprev := st212_p486
  have hstep := st212_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p488 : ((8592877836061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT212 (i+1))
      = (∑ i ∈ Finset.range 487, stT212 (i+1)) + stT212 488 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 487
    simpa using h
  have hprev := st212_p487
  have hstep := st212_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p489 : ((9044908332341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT212 (i+1))
      = (∑ i ∈ Finset.range 488, stT212 (i+1)) + stT212 489 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 488
    simpa using h
  have hprev := st212_p488
  have hstep := st212_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p490 : ((590606830487/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT212 (i+1))
      = (∑ i ∈ Finset.range 489, stT212 (i+1)) + stT212 490 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 489
    simpa using h
  have hprev := st212_p489
  have hstep := st212_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p491 : ((9733006212077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT212 (i+1))
      = (∑ i ∈ Finset.range 490, stT212 (i+1)) + stT212 491 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 490
    simpa using h
  have hprev := st212_p490
  have hstep := st212_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p492 : ((9843377588621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT212 (i+1))
      = (∑ i ∈ Finset.range 491, stT212 (i+1)) + stT212 492 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 491
    simpa using h
  have hprev := st212_p491
  have hstep := st212_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p493 : ((9761366907467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT212 (i+1))
      = (∑ i ∈ Finset.range 492, stT212 (i+1)) + stT212 493 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 492
    simpa using h
  have hprev := st212_p492
  have hstep := st212_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p494 : ((1900523712991/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT212 (i+1))
      = (∑ i ∈ Finset.range 493, stT212 (i+1)) + stT212 494 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 493
    simpa using h
  have hprev := st212_p493
  have hstep := st212_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p495 : ((227866584281/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT212 (i+1))
      = (∑ i ∈ Finset.range 494, stT212 (i+1)) + stT212 495 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 494
    simpa using h
  have hprev := st212_p494
  have hstep := st212_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p496 : ((1083492642337/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT212 (i+1))
      = (∑ i ∈ Finset.range 495, stT212 (i+1)) + stT212 496 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 495
    simpa using h
  have hprev := st212_p495
  have hstep := st212_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p497 : ((4121449295021/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT212 (i+1))
      = (∑ i ∈ Finset.range 496, stT212 (i+1)) + stT212 497 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 496
    simpa using h
  have hprev := st212_p496
  have hstep := st212_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p498 : ((1978867090863/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT212 (i+1))
      = (∑ i ∈ Finset.range 497, stT212 (i+1)) + stT212 498 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 497
    simpa using h
  have hprev := st212_p497
  have hstep := st212_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p499 : ((3871800312713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT212 (i+1))
      = (∑ i ∈ Finset.range 498, stT212 (i+1)) + stT212 499 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 498
    simpa using h
  have hprev := st212_p498
  have hstep := st212_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_p500 : ((1551437659601/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT212 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT212 (i+1))
      = (∑ i ∈ Finset.range 499, stT212 (i+1)) + stT212 500 := by
    have h := Finset.sum_range_succ (fun i => stT212 (i+1)) 499
    simpa using h
  have hprev := st212_p499
  have hstep := st212_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st212_s500 :
    |Real.sin (((212 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))
      - ((-999537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -3850897/10000000) (δ := 10709/1000000000) (ψ := -431649/1000000) 212 210
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 212`** (evaluated boundary). -/
theorem station_212_sign : hardyG ((((212:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 212 500 (by norm_num) (by norm_num)
    ((-431649/1000000 : ℚ) : ℝ)
  have hchain := st212_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT212 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((212 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-431649/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st212_c500
  have hsinb := abs_le.mp st212_s500
  have hbdy_lo : ((2915498544801/27658000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((212 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ))) / 2
          - ((((212:ℕ)):ℝ))
            * Real.sin (((212 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-431649/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((212:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((212:ℝ) * Real.log (500:ℝ) - ((-431649/1000000 : ℚ) : ℝ))) / 2
        - ((212:ℝ)) * Real.sin ((212:ℝ) * Real.log (500:ℝ) - ((-431649/1000000 : ℚ) : ℝ))
        ≥ ((84750401/400000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((212:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((84750401/400000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((84750401/400000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((84750401/400000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((212:ℕ)):ℝ))+1) * (((((212:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1815642106137/5000000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1551437659601/2000000000000 : ℚ) : ℝ) + ((2915498544801/27658000000000 : ℚ) : ℝ)
      - ((1815642106137/5000000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-431649/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((212:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-431649/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((212:ℕ)):ℝ)))).re
      - Real.sin ((-431649/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((212:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((212:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((212:ℕ)):ℝ))
      = (((((212:ℕ)):ℝ)) * (Real.log ((((212:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((212:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_212
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
  have hθwin : |(((-431649/1000000 : ℚ) : ℝ) + ((43:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((212:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((212:ℕ)):ℝ)))
    (φ := ((-431649/1000000 : ℚ) : ℝ) + ((43:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-431649/1000000 : ℚ) : ℝ) + ((43:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-431649/1000000 : ℚ)) : ℝ) - Real.pi) + ((43:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-431649/1000000 : ℚ)) : ℝ) - Real.pi) 43).1,
    (cos_sin_shift ((((-431649/1000000 : ℚ)) : ℝ) - Real.pi) 43).2]
  exact cos_sin_flip ((-431649/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_212_sign
end AxiomAudit
