import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 158` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT158 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((158 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))

theorem st158_c1 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((106177/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 694899/5000000) (δ := 201/1000000000) (ψ := -555919/1000000) 158 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t1 : ((424683/500000 : ℚ) : ℝ) ≤ stT158 1 := by
  have hc : ((424683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((424683/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((424683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c2 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-496557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7560417/10000000) (δ := 7931/1000000000) (ψ := -555919/1000000) 158 18
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t2 : ((-438920636197/625000000000 : ℚ) : ℝ) ≤ stT158 2 := by
  have hc : ((-248291/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-438920636197/625000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-248291/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c3 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-8797/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -896267/2000000) (δ := 8003/1000000000) (ψ := -555919/1000000) 158 28
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t3 : ((-50801052897/400000000000 : ℚ) : ℝ) ≤ stT158 3 := by
  have hc : ((-8799/40000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50801052897/400000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-8799/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c4 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((474451/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -802649/10000000) (δ := 161/20000000) (ψ := -555919/1000000) 158 35
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t4 : ((237213/500000 : ℚ) : ℝ) ≤ stT158 4 := by
  have hc : ((237213/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237213/500000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((237213/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c5 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-232341/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3454353/5000000) (δ := 1999/250000000) (ψ := -555919/1000000) 158 41
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t5 : ((-259779113019/625000000000 : ℚ) : ℝ) ≤ stT158 5 := by
  have hc : ((-464707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-259779113019/625000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-464707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c6 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((613293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2276433/10000000) (δ := 3989/500000000) (ψ := -555919/1000000) 158 45
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t6 : ((1251776754563/5000000000000 : ℚ) : ℝ) ≤ stT158 6 := by
  have hc : ((613243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1251776754563/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((613243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c7 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((991083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 334107/10000000) (δ := 8053/1000000000) (ψ := -555919/1000000) 158 49
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t7 : ((936437983063/2500000000000 : ℚ) : ℝ) ≤ stT158 7 := by
  have hc : ((991033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((936437983063/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((991033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c8 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-14503/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 74439/125000) (δ := 319/40000000) (ψ := -555919/1000000) 158 52
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t8 : ((-3204961571/12500000000 : ℚ) : ℝ) ≤ stT158 8 := by
  have hc : ((-1813/2500 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3204961571/12500000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-1813/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c9 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-270409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1071103/2000000) (δ := 7907/1000000000) (ψ := -555919/1000000) 158 55
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t9 : ((-225361711739/1250000000000 : ℚ) : ℝ) ≤ stT158 9 := by
  have hc : ((-135217/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225361711739/1250000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-135217/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c10 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((998177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -150977/10000000) (δ := 4009/500000000) (ψ := -555919/1000000) 158 58
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t10 : ((3156354055179/10000000000000 : ℚ) : ℝ) ≤ stT158 10 := by
  have hc : ((998127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3156354055179/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((998127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c11 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-75879/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9729/16000) (δ := 7971/1000000000) (ψ := -555919/1000000) 158 60
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t11 : ((-28599863847/125000000000 : ℚ) : ℝ) ≤ stT158 11 := by
  have hc : ((-18971/25000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28599863847/125000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-18971/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c12 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-890621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3336881/5000000) (δ := 8049/1000000000) (ψ := -555919/1000000) 158 63
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t12 : ((-80348321581/312500000000 : ℚ) : ℝ) ≤ stT158 12 := by
  have hc : ((-890671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80348321581/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-890671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c13 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-425617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3236411/5000000) (δ := 1607/200000000) (ψ := -555919/1000000) 158 65
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t13 : ((-590259256321/2500000000000 : ℚ) : ℝ) ≤ stT158 13 := by
  have hc : ((-212821/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-590259256321/2500000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-212821/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c14 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-476947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11347/16000) (δ := 991/125000000) (ψ := -555919/1000000) 158 66
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t14 : ((-318690391959/1250000000000 : ℚ) : ℝ) ≤ stT158 14 := by
  have hc : ((-119243/125000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-318690391959/1250000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-119243/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c15 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((388993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183009/625000) (δ := 7913/1000000000) (ψ := -555919/1000000) 158 68
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t15 : ((251061539671/2500000000000 : ℚ) : ℝ) ≤ stT158 15 := by
  have hc : ((388943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((251061539671/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((388943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c16 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((364193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -119803/400000) (δ := 247/31250000) (ψ := -555919/1000000) 158 70
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t16 : ((364143/4000000 : ℚ) : ℝ) ≤ stT158 16 := by
  have hc : ((364143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((364143/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((364143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c17 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-251331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5243679/10000000) (δ := 8011/1000000000) (ψ := -555919/1000000) 158 71
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t17 : ((-152407008523/1250000000000 : ℚ) : ℝ) ≤ stT158 17 := by
  have hc : ((-62839/125000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152407008523/1250000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-62839/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c18 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((132533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -89867/250000) (δ := 7977/1000000000) (ψ := -555919/1000000) 158 73
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t18 : ((156132672813/5000000000000 : ℚ) : ℝ) ≤ stT158 18 := by
  have hc : ((132483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156132672813/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((132483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c19 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((681079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2053901/10000000) (δ := 7933/1000000000) (ψ := -555919/1000000) 158 74
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t19 : ((1562387447553/10000000000000 : ℚ) : ℝ) ≤ stT158 19 := by
  have hc : ((681029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1562387447553/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((681029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c20 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-878121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6606791/10000000) (δ := 7963/1000000000) (ψ := -555919/1000000) 158 75
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t20 : ((-490912517907/2500000000000 : ℚ) : ℝ) ≤ stT158 20 := by
  have hc : ((-878171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-490912517907/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-878171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c21 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-150101/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2768503/5000000) (δ := 4027/500000000) (ψ := -555919/1000000) 158 77
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t21 : ((-655149054633/5000000000000 : ℚ) : ℝ) ≤ stT158 21 := by
  have hc : ((-300227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-655149054633/5000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-300227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c22 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((410469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -286957/1000000) (δ := 8041/1000000000) (ψ := -555919/1000000) 158 78
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t22 : ((875016180933/10000000000000 : ℚ) : ℝ) ≤ stT158 22 := by
  have hc : ((410419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((875016180933/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((410419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c23 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((918063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15923/156250) (δ := 3967/500000000) (ψ := -555919/1000000) 158 79
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t23 : ((239273662359/1250000000000 : ℚ) : ℝ) ≤ stT158 23 := by
  have hc : ((918013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239273662359/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((918013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c24 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((199887/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 84007/10000000) (δ := 997/125000000) (ψ := -555919/1000000) 158 80
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t24 : ((407997127357/2000000000000 : ℚ) : ℝ) ≤ stT158 24 := by
  have hc : ((199877/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((407997127357/2000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((199877/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c25 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((122501/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 250367/5000000) (δ := 8083/1000000000) (ψ := -555919/1000000) 158 81
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t25 : ((489979/2500000 : ℚ) : ℝ) ≤ stT158 25 := by
  have hc : ((489979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((489979/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((489979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c26 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((993511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 284947/10000000) (δ := 799/100000000) (ψ := -555919/1000000) 158 82
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t26 : ((1948336968221/10000000000000 : ℚ) : ℝ) ≤ stT158 26 := by
  have hc : ((993461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1948336968221/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((993461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c27 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((122351/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -257799/5000000) (δ := 3953/500000000) (ψ := -555919/1000000) 158 83
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t27 : ((1883619771/10000000000 : ℚ) : ℝ) ≤ stT158 27 := by
  have hc : ((489379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1883619771/10000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((489379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c28 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((36811/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -23229/125000) (δ := 3999/500000000) (ψ := -555919/1000000) 158 84
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t28 : ((69561513087/500000000000 : ℚ) : ℝ) ≤ stT158 28 := by
  have hc : ((73617/100000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69561513087/500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((73617/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c29 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((5537/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -185261/500000) (δ := 8091/1000000000) (ψ := -555919/1000000) 158 85
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t29 : ((82209166263/5000000000000 : ℚ) : ℝ) ≤ stT158 29 := by
  have hc : ((44271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82209166263/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((44271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c30 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-743333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -602209/1000000) (δ := 8019/1000000000) (ψ := -555919/1000000) 158 86
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t30 : ((-678612782593/5000000000000 : ℚ) : ℝ) ≤ stT158 30 := by
  have hc : ((-743383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-678612782593/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-743383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c31 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-932463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10828/15625) (δ := 499/62500000) (ψ := -555919/1000000) 158 86
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t31 : ((-837421851851/5000000000000 : ℚ) : ℝ) ≤ stT158 31 := by
  have hc : ((-932513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-837421851851/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-932513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c32 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((8209/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3762693/10000000) (δ := 8077/1000000000) (ψ := -555919/1000000) 158 87
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t32 : ((29001085113/2500000000000 : ℚ) : ℝ) ≤ stT158 32 := by
  have hc : ((32811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29001085113/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((32811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c33 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((99649/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26189/1250000) (δ := 797/100000000) (ψ := -555919/1000000) 158 88
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t33 : ((5420558867/31250000000 : ℚ) : ℝ) ≤ stT158 33 := by
  have hc : ((24911/25000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5420558867/31250000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((24911/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c34 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((22019/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -926629/2500000) (δ := 397/50000000) (ψ := -555919/1000000) 158 89
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t34 : ((15096326961/1000000000000 : ℚ) : ℝ) ≤ stT158 34 := by
  have hc : ((44013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15096326961/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((44013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c35 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-62439/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3871773/5000000) (δ := 8063/1000000000) (ψ := -555919/1000000) 158 89
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t35 : ((-844371886933/5000000000000 : ℚ) : ℝ) ≤ stT158 35 := by
  have hc : ((-499537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-844371886933/5000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-499537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c36 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((75207/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3163089/10000000) (δ := 503/62500000) (ψ := -555919/1000000) 158 90
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t36 : ((125324116537/2500000000000 : ℚ) : ℝ) ≤ stT158 36 := by
  have hc : ((150389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125324116537/2500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((150389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c37 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((771941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -172227/1000000) (δ := 503/62500000) (ψ := -555919/1000000) 158 91
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t37 : ((1268980313199/10000000000000 : ℚ) : ℝ) ≤ stT158 37 := by
  have hc : ((771891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1268980313199/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((771891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c38 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-5797/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3448147/5000000) (δ := 7941/1000000000) (ψ := -555919/1000000) 158 92
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t38 : ((-30094359351/200000000000 : ℚ) : ℝ) ≤ stT158 38 := by
  have hc : ((-92757/100000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30094359351/200000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-92757/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c39 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((111643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3364029/10000000) (δ := 4031/500000000) (ψ := -555919/1000000) 158 92
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t39 : ((89365891329/2500000000000 : ℚ) : ℝ) ≤ stT158 39 := by
  have hc : ((55809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89365891329/2500000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((55809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c40 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((591917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -585851/2500000) (δ := 4017/500000000) (ψ := -555919/1000000) 158 93
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t40 : ((467911702323/5000000000000 : ℚ) : ℝ) ≤ stT158 40 := by
  have hc : ((591867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((467911702323/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((591867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c41 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-246071/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7410173/10000000) (δ := 4017/500000000) (ψ := -555919/1000000) 158 93
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t41 : ((-384317953123/2500000000000 : ℚ) : ℝ) ≤ stT158 41 := by
  have hc : ((-492167/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-384317953123/2500000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-492167/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c42 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((883129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 610381/5000000) (δ := 7927/1000000000) (ψ := -555919/1000000) 158 94
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t42 : ((1362620038607/10000000000000 : ℚ) : ℝ) ≤ stT158 42 := by
  have hc : ((883079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1362620038607/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((883079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c43 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-242457/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2596327/5000000) (δ := 8019/1000000000) (ψ := -555919/1000000) 158 95
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t43 : ((-92445413813/1250000000000 : ℚ) : ℝ) ≤ stT158 43 := by
  have hc : ((-121241/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92445413813/1250000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-121241/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c44 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((3879/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3888199/10000000) (δ := 499/62500000) (ψ := -555919/1000000) 158 95
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t44 : ((2914482637/1250000000000 : ℚ) : ℝ) ≤ stT158 44 := by
  have hc : ((7733/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2914482637/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((7733/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c45 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((383509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -91969/312500) (δ := 8091/1000000000) (ψ := -555919/1000000) 158 96
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t45 : ((571626549349/10000000000000 : ℚ) : ℝ) ≤ stT158 45 := by
  have hc : ((383459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((571626549349/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((383459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c46 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-331443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5738657/10000000) (δ := 989/125000000) (ψ := -555919/1000000) 158 96
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t46 : ((-6109038107/62500000000 : ℚ) : ℝ) ≤ stT158 46 := by
  have hc : ((-82867/125000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6109038107/62500000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-82867/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c47 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((207773/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -737159/5000000) (δ := 1601/200000000) (ψ := -555919/1000000) 158 97
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t47 : ((606099291129/5000000000000 : ℚ) : ℝ) ≤ stT158 47 := by
  have hc : ((415521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((606099291129/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((415521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c48 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-919149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 273671/400000) (δ := 1601/200000000) (ψ := -555919/1000000) 158 97
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t48 : ((-82921860989/625000000000 : ℚ) : ℝ) ≤ stT158 48 := by
  have hc : ((-919199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82921860989/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-919199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c49 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((958631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -180401/2500000) (δ := 1581/200000000) (ψ := -555919/1000000) 158 98
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t49 : ((1369401017751/10000000000000 : ℚ) : ℝ) ≤ stT158 49 := by
  have hc : ((958581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1369401017751/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((958581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c50 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-485883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3629251/5000000) (δ := 1581/200000000) (ψ := -555919/1000000) 158 98
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t50 : ((-85897237039/625000000000 : ℚ) : ℝ) ≤ stT158 50 := by
  have hc : ((-121477/125000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85897237039/625000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-121477/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c51 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((968671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -313717/5000000) (δ := 2003/250000000) (ψ := -555919/1000000) 158 99
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t51 : ((33908515347/250000000000 : ℚ) : ℝ) ≤ stT158 51 := by
  have hc : ((968621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33908515347/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((968621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c52 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-29619/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1408543/2000000) (δ := 7991/1000000000) (ψ := -555919/1000000) 158 99
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t52 : ((-657221514679/5000000000000 : ℚ) : ℝ) ≤ stT158 52 := by
  have hc : ((-473929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-657221514679/5000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-473929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c53 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((112201/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1141209/10000000) (δ := 7919/1000000000) (ψ := -555919/1000000) 158 100
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t53 : ((123289015659/1000000000000 : ℚ) : ℝ) ≤ stT158 53 := by
  have hc : ((448779/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123289015659/1000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((448779/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c54 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-159853/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 624217/1000000) (δ := 2021/250000000) (ψ := -555919/1000000) 158 100
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t54 : ((-54386511641/500000000000 : ℚ) : ℝ) ≤ stT158 54 := by
  have hc : ((-159863/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54386511641/500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-159863/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c55 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((631617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1108949/5000000) (δ := 8027/1000000000) (ψ := -555919/1000000) 158 101
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t55 : ((851604311233/10000000000000 : ℚ) : ℝ) ≤ stT158 55 := by
  have hc : ((631567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((851604311233/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((631567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c56 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-379233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4899409/10000000) (δ := 997/125000000) (ψ := -555919/1000000) 158 101
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t56 : ((-506838527881/10000000000000 : ℚ) : ℝ) ≤ stT158 56 := by
  have hc : ((-379283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-506838527881/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-379283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c57 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((43897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -954303/2500000) (δ := 3967/500000000) (ψ := -555919/1000000) 158 102
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t57 : ((14519188651/2500000000000 : ℚ) : ℝ) ≤ stT158 57 := by
  have hc : ((43847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14519188651/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((43847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c58 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((10709/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3052549/10000000) (δ := 3967/500000000) (ψ := -555919/1000000) 158 102
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t58 : ((28119101427/625000000000 : ℚ) : ℝ) ≤ stT158 58 := by
  have hc : ((171319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28119101427/625000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((171319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c59 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-710673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2951563/5000000) (δ := 8041/1000000000) (ψ := -555919/1000000) 158 103
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t59 : ((-92528316647/1000000000000 : ℚ) : ℝ) ≤ stT158 59 := by
  have hc : ((-710723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92528316647/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-710723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c60 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((478507/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 367839/5000000) (δ := 3981/500000000) (ψ := -555919/1000000) 158 103
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t60 : ((154429347777/1250000000000 : ℚ) : ℝ) ≤ stT158 60 := by
  have hc : ((239241/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154429347777/1250000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((239241/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c61 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-972353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 454047/625000) (δ := 8041/1000000000) (ψ := -555919/1000000) 158 103
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t61 : ((-1245034656707/10000000000000 : ℚ) : ℝ) ≤ stT158 61 := by
  have hc : ((-972403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1245034656707/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-972403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c62 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((138171/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1010157/5000000) (δ := 1987/250000000) (ψ := -555919/1000000) 158 104
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t62 : ((175464608161/2000000000000 : ℚ) : ℝ) ≤ stT158 62 := by
  have hc : ((138161/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175464608161/2000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((138161/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c63 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-148589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1074961/2500000) (δ := 1987/250000000) (ψ := -555919/1000000) 158 104
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t63 : ((-93633800299/5000000000000 : ℚ) : ℝ) ≤ stT158 63 := by
  have hc : ((-148639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93633800299/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-148639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c64 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-773/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5187541/10000000) (δ := 1987/250000000) (ψ := -555919/1000000) 158 105
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t64 : ((-24158769327/400000000000 : ℚ) : ℝ) ≤ stT158 64 := by
  have hc : ((-19327/40000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24158769327/400000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-19327/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c65 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((930637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 468309/5000000) (δ := 1987/250000000) (ψ := -555919/1000000) 158 105
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t65 : ((1154250793689/10000000000000 : ℚ) : ℝ) ≤ stT158 65 := by
  have hc : ((930587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1154250793689/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((930587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c66 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-468879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6967281/10000000) (δ := 1611/200000000) (ψ := -555919/1000000) 158 105
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t66 : ((-14429524179/125000000000 : ℚ) : ℝ) ≤ stT158 66 := by
  have hc : ((-58613/62500 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14429524179/125000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-58613/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c67 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((217713/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -350089/1250000) (δ := 7963/1000000000) (ψ := -555919/1000000) 158 106
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t67 : ((16621757717/312500000000 : ℚ) : ℝ) ≤ stT158 67 := by
  have hc : ((27211/62500 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16621757717/312500000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((27211/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c68 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((13727/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 762813/2500000) (δ := 201/25000000) (ψ := -555919/1000000) 158 106
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t68 : ((332880111/8000000000 : ℚ) : ℝ) ≤ stT158 68 := by
  have hc : ((549/1600 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((332880111/8000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((549/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c69 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-231651/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1378037/2000000) (δ := 7933/1000000000) (ψ := -555919/1000000) 158 107
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t69 : ((-557780378893/5000000000000 : ℚ) : ℝ) ≤ stT158 69 := by
  have hc : ((-463327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-557780378893/5000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-463327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c70 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((221441/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -150831/1250000) (δ := 807/100000000) (ψ := -555919/1000000) 158 107
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t70 : ((132328771599/1250000000000 : ℚ) : ℝ) ≤ stT158 70 := by
  have hc : ((442857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132328771599/1250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((442857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c71 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-186611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4396269/10000000) (δ := 807/100000000) (ψ := -555919/1000000) 158 107
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t71 : ((-110762957451/5000000000000 : ℚ) : ℝ) ≤ stT158 71 := by
  have hc : ((-186661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110762957451/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-186661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c72 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-67727/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2893553/5000000) (δ := 7977/1000000000) (ψ := -555919/1000000) 158 108
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t72 : ((-1247233981/15625000000 : ℚ) : ℝ) ≤ stT158 72 := by
  have hc : ((-16933/25000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1247233981/15625000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-16933/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c73 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((495417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -338753/10000000) (δ := 4013/500000000) (ψ := -555919/1000000) 158 108
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t73 : ((18119132691/156250000000 : ℚ) : ℝ) ≤ stT158 73 := by
  have hc : ((15481/15625 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18119132691/156250000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((15481/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c74 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-214501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5035459/10000000) (δ := 4013/500000000) (ψ := -555919/1000000) 158 108
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t74 : ((-124690770451/2500000000000 : ℚ) : ℝ) ≤ stT158 74 := by
  have hc : ((-107263/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124690770451/2500000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-107263/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c75 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-54581/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5370379/10000000) (δ := 2021/250000000) (ψ := -555919/1000000) 158 109
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t75 : ((-31515254393/500000000000 : ℚ) : ℝ) ≤ stT158 75 := by
  have hc : ((-27293/50000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31515254393/500000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-27293/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c76 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((199693/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5541/400000) (δ := 2021/250000000) (ψ := -555919/1000000) 158 109
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t76 : ((114525988137/1000000000000 : ℚ) : ℝ) ≤ stT158 76 := by
  have hc : ((199683/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114525988137/1000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((199683/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c77 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-212601/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2512477/5000000) (δ := 7919/1000000000) (ψ := -555919/1000000) 158 109
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t77 : ((-60577466339/1250000000000 : ℚ) : ℝ) ≤ stT158 77 := by
  have hc : ((-106313/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60577466339/1250000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-106313/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c78 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-154003/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2793083/5000000) (δ := 7991/1000000000) (ψ := -555919/1000000) 158 110
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t78 : ((-174388362309/2500000000000 : ℚ) : ℝ) ≤ stT158 78 := by
  have hc : ((-308031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174388362309/2500000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-308031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c79 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((243881/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -554261/10000000) (δ := 7991/1000000000) (ψ := -555919/1000000) 158 110
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t79 : ((548746558119/5000000000000 : ℚ) : ℝ) ≤ stT158 79 := by
  have hc : ((487737/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((548746558119/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((487737/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c80 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-193717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 882873/2000000) (δ := 7991/1000000000) (ψ := -555919/1000000) 158 110
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t80 : ((-108319047039/5000000000000 : ℚ) : ℝ) ≤ stT158 80 := by
  have hc : ((-193767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108319047039/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-193767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c81 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-832657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6386711/10000000) (δ := 1581/200000000) (ψ := -555919/1000000) 158 111
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t81 : ((-115653842523/1250000000000 : ℚ) : ℝ) ≤ stT158 81 := by
  have hc : ((-832707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115653842523/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-832707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c82 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((816191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1540021/10000000) (δ := 4049/500000000) (ψ := -555919/1000000) 158 111
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t82 : ((180255349683/2000000000000 : ℚ) : ℝ) ≤ stT158 82 := by
  have hc : ((816141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180255349683/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((816141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c83 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((33537/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 811983/2500000) (δ := 4049/500000000) (ψ := -555919/1000000) 158 111
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t83 : ((73609518983/2500000000000 : ℚ) : ℝ) ≤ stT158 83 := by
  have hc : ((134123/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73609518983/2500000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((134123/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c84 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-24969/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7729453/10000000) (δ := 15997/1000000000) (ψ := -555919/1000000) 158 112
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t84 : ((-10897916029/100000000000 : ℚ) : ℝ) ≤ stT158 84 := by
  have hc : ((-99881/100000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10897916029/100000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-99881/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c85 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((13673/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -610969/2000000) (δ := 7997/1000000000) (ψ := -555919/1000000) 158 112
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t85 : ((3707069373/100000000000 : ℚ) : ℝ) ≤ stT158 85 := by
  have hc : ((13671/40000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3707069373/100000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((13671/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c86 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((20259/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 62603/400000) (δ := 7997/1000000000) (ψ := -555919/1000000) 158 112
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t86 : ((87377915137/1000000000000 : ℚ) : ℝ) ≤ stT158 86 := by
  have hc : ((81031/100000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87377915137/1000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((81031/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c87 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-9649/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6131631/10000000) (δ := 4003/500000000) (ψ := -555919/1000000) 158 112
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t87 : ((-82763907261/1000000000000 : ℚ) : ℝ) ≤ stT158 87 := by
  have hc : ((-77197/100000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82763907261/1000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-77197/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c88 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-219283/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1265499/2500000) (δ := 7913/1000000000) (ψ := -555919/1000000) 158 113
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t88 : ((-14611450327/312500000000 : ℚ) : ℝ) ≤ stT158 88 := by
  have hc : ((-54827/125000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14611450327/312500000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-54827/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c89 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((485731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -299347/5000000) (δ := 809/100000000) (ψ := -555919/1000000) 158 113
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t89 : ((257423451441/2500000000000 : ℚ) : ℝ) ≤ stT158 89 := by
  have hc : ((242853/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((257423451441/2500000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((242853/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c90 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((44877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 95369/250000) (δ := 7913/1000000000) (ψ := -555919/1000000) 158 113
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t90 : ((11812945521/2500000000000 : ℚ) : ℝ) ≤ stT158 90 := by
  have hc : ((44827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11812945521/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((44827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c91 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-495769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7528513/10000000) (δ := 15983/1000000000) (ψ := -555919/1000000) 158 114
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t91 : ((-51973341329/500000000000 : ℚ) : ℝ) ≤ stT158 91 := by
  have hc : ((-247897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51973341329/500000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-247897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c92 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((282291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1605769/5000000) (δ := 7983/1000000000) (ψ := -555919/1000000) 158 114
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t92 : ((73564140963/2500000000000 : ℚ) : ℝ) ≤ stT158 92 := by
  have hc : ((282241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73564140963/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((282241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c93 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((911653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66173/625000) (δ := 401/50000000) (ψ := -555919/1000000) 158 114
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t93 : ((945287642453/10000000000000 : ℚ) : ℝ) ≤ stT158 93 := by
  have hc : ((911603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((945287642453/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((911603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c94 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-516337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5283411/10000000) (δ := 7983/1000000000) (ψ := -555919/1000000) 158 114
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t94 : ((-266306456157/5000000000000 : ℚ) : ℝ) ≤ stT158 94 := by
  have hc : ((-516387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-266306456157/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-516387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c95 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-159971/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6244623/10000000) (δ := 2019/250000000) (ψ := -555919/1000000) 158 115
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t95 : ((-164137146399/2000000000000 : ℚ) : ℝ) ≤ stT158 95 := by
  have hc : ((-159981/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164137146399/2000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-159981/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c96 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((664939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2108459/10000000) (δ := 7927/1000000000) (ψ := -555919/1000000) 158 115
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t96 : ((33929950559/500000000000 : ℚ) : ℝ) ≤ stT158 96 := by
  have hc : ((664889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33929950559/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((664889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c97 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((350521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1984847/10000000) (δ := 7927/1000000000) (ψ := -555919/1000000) 158 115
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t97 : ((5560542369/78125000000 : ℚ) : ℝ) ≤ stT158 97 := by
  have hc : ((10953/15625 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5560542369/78125000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((10953/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c98 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-747087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1509041/2500000) (δ := 2019/250000000) (ψ := -555919/1000000) 158 115
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t98 : ((-754722681961/10000000000000 : ℚ) : ℝ) ≤ stT158 98 := by
  have hc : ((-747137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-754722681961/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-747137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c99 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-639497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5661601/10000000) (δ := 7969/1000000000) (ψ := -555919/1000000) 158 116
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t99 : ((-321384518893/5000000000000 : ℚ) : ℝ) ≤ stT158 99 := by
  have hc : ((-639547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-321384518893/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-639547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c100 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((12182/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -422933/2500000) (δ := 4017/500000000) (ψ := -555919/1000000) 158 116
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t100 : ((389798610201/5000000000000 : ℚ) : ℝ) ≤ stT158 100 := by
  have hc : ((389799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((389798610201/5000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((389799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c101 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((9768/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 559669/2500000) (δ := 4017/500000000) (ψ := -555919/1000000) 158 116
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t101 : ((310999809387/5000000000000 : ℚ) : ℝ) ≤ stT158 101 := by
  have hc : ((312551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((310999809387/5000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((312551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c102 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-77159/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3065167/5000000) (δ := 7969/1000000000) (ψ := -555919/1000000) 158 116
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t102 : ((-4775236267/62500000000 : ℚ) : ℝ) ≤ stT158 102 := by
  have hc : ((-19291/25000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4775236267/62500000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-19291/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c103 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-164619/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -572397/1000000) (δ := 8061/1000000000) (ψ := -555919/1000000) 158 117
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t103 : ((-32443271179/500000000000 : ℚ) : ℝ) ≤ stT158 103 := by
  have hc : ((-329263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32443271179/500000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-329263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c104 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((722761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1907519/10000000) (δ := 3971/500000000) (ψ := -555919/1000000) 158 117
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t104 : ((35433797619/500000000000 : ℚ) : ℝ) ≤ stT158 104 := by
  have hc : ((722711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35433797619/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((722711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c105 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((183097/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1872433/10000000) (δ := 8061/1000000000) (ψ := -555919/1000000) 158 117
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t105 : ((3573443271/50000000000 : ℚ) : ℝ) ≤ stT158 105 := by
  have hc : ((366169/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3573443271/50000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((366169/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c106 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-625531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 140413/250000) (δ := 3971/500000000) (ψ := -555919/1000000) 158 117
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t106 : ((-303809033583/5000000000000 : ℚ) : ℝ) ≤ stT158 106 := by
  have hc : ((-625581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-303809033583/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-625581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c107 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-831717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -797809/1250000) (δ := 8049/1000000000) (ψ := -555919/1000000) 158 118
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t107 : ((-804099934279/10000000000000 : ℚ) : ℝ) ≤ stT158 107 := by
  have hc : ((-831767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-804099934279/10000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-831767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c108 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((93699/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -338503/1250000) (δ := 8049/1000000000) (ψ := -555919/1000000) 158 118
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t108 : ((360608961/8000000000 : ℚ) : ℝ) ≤ stT158 108 := by
  have hc : ((93689/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((360608961/8000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((93689/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c109 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((931233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 932533/10000000) (δ := 8049/1000000000) (ψ := -555919/1000000) 158 118
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t109 : ((445955644079/5000000000000 : ℚ) : ℝ) ≤ stT158 109 := by
  have hc : ((931183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((445955644079/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((931183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c110 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-242703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 453987/1000000) (δ := 3977/500000000) (ψ := -555919/1000000) 158 118
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t110 : ((-231456003639/10000000000000 : ℚ) : ℝ) ≤ stT158 110 := by
  have hc : ((-242753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-231456003639/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-242753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c111 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-248643/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7593383/10000000) (δ := 8047/1000000000) (ψ := -555919/1000000) 158 119
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t111 : ((-236013357069/2500000000000 : ℚ) : ℝ) ≤ stT158 111 := by
  have hc : ((-497311/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236013357069/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-497311/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c112 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-24749/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2025393/5000000) (δ := 8047/1000000000) (ψ := -555919/1000000) 158 119
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t112 : ((-731539059/156250000000 : ℚ) : ℝ) ≤ stT158 112 := by
  have hc : ((-12387/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-731539059/156250000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-12387/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c113 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((488397/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -539631/10000000) (δ := 8047/1000000000) (ψ := -555919/1000000) 158 119
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t113 : ((1435691587/15625000000 : ℚ) : ℝ) ≤ stT158 113 := by
  have hc : ((122093/125000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1435691587/15625000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((122093/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c114 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((76883/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 735139/2500000) (δ := 8047/1000000000) (ψ := -555919/1000000) 158 119
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t114 : ((14399619741/400000000000 : ℚ) : ℝ) ≤ stT158 114 := by
  have hc : ((76873/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14399619741/400000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((76873/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c115 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-416733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 199699/312500) (δ := 1989/250000000) (ψ := -555919/1000000) 158 119
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t115 : ((-38862891879/500000000000 : ℚ) : ℝ) ≤ stT158 115 := by
  have hc : ((-208379/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38862891879/500000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-208379/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c116 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-35457/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1179537/2000000) (δ := 8063/1000000000) (ψ := -555919/1000000) 158 120
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t116 : ((-65846660363/1000000000000 : ℚ) : ℝ) ≤ stT158 116 := by
  have hc : ((-70919/100000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65846660363/1000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-70919/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c117 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((134479/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -626771/2500000) (δ := 8063/1000000000) (ψ := -555919/1000000) 158 120
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t117 : ((497257117/10000000000 : ℚ) : ℝ) ≤ stT158 117 := by
  have hc : ((268933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((497257117/10000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((268933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c118 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((471067/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 427321/5000000) (δ := 397/50000000) (ψ := -555919/1000000) 158 120
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t118 : ((108407254527/1250000000000 : ℚ) : ℝ) ≤ stT158 118 := by
  have hc : ((235521/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108407254527/1250000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((235521/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c119 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-104201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65437/156250) (δ := 397/50000000) (ψ := -555919/1000000) 158 120
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t119 : ((-95566787449/10000000000000 : ℚ) : ℝ) ≤ stT158 119 := by
  have hc : ((-104251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95566787449/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-104251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c120 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-989619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7493447/10000000) (δ := 8063/1000000000) (ψ := -555919/1000000) 158 120
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t120 : ((-903440129699/10000000000000 : ℚ) : ℝ) ≤ stT158 120 := by
  have hc : ((-989669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-903440129699/10000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-989669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c121 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-98229/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4936491/10000000) (δ := 8033/1000000000) (ψ := -555919/1000000) 158 121
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t121 : ((-178620926953/5000000000000 : ℚ) : ℝ) ≤ stT158 121 := by
  have hc : ((-196483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178620926953/5000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-196483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c122 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((781221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1685443/10000000) (δ := 797/100000000) (ψ := -555919/1000000) 158 121
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t122 : ((707238633047/10000000000000 : ℚ) : ℝ) ≤ stT158 122 := by
  have hc : ((781171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((707238633047/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((781171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c123 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((816413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 76953/500000) (δ := 8033/1000000000) (ψ := -555919/1000000) 158 121
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t123 : ((736089209847/10000000000000 : ℚ) : ℝ) ≤ stT158 123 := by
  have hc : ((816363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((736089209847/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((816363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c124 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-318537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2368727/5000000) (δ := 8033/1000000000) (ψ := -555919/1000000) 158 121
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t124 : ((-286099727849/10000000000000 : ℚ) : ℝ) ≤ stT158 124 := by
  have hc : ((-318587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286099727849/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-318587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c125 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-999747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -779779/1000000) (δ := 3963/500000000) (ψ := -555919/1000000) 158 122
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t125 : ((-223561607779/2500000000000 : ℚ) : ℝ) ≤ stT158 125 := by
  have hc : ((-999797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223561607779/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-999797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c126 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-71331/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4650351/10000000) (δ := 3963/500000000) (ψ := -555919/1000000) 158 122
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t126 : ((-127115710377/5000000000000 : ℚ) : ℝ) ≤ stT158 126 := by
  have hc : ((-142687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127115710377/5000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-142687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c127 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((409499/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -381959/2500000) (δ := 8077/1000000000) (ψ := -555919/1000000) 158 122
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t127 : ((45418651343/625000000000 : ℚ) : ℝ) ≤ stT158 127 := by
  have hc : ((204737/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45418651343/625000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((204737/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c128 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((809151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 392557/2500000) (δ := 8077/1000000000) (ψ := -555919/1000000) 158 122
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t128 : ((715150619183/10000000000000 : ℚ) : ℝ) ≤ stT158 128 := by
  have hc : ((809101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((715150619183/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((809101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c129 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-282963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4644197/10000000) (δ := 8077/1000000000) (ψ := -555919/1000000) 158 122
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t129 : ((-249179078863/10000000000000 : ℚ) : ℝ) ≤ stT158 129 := by
  have hc : ((-283013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-249179078863/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-283013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c130 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-997963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7694387/10000000) (δ := 8077/1000000000) (ψ := -555919/1000000) 158 122
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t130 : ((-875316283767/10000000000000 : ℚ) : ℝ) ≤ stT158 130 := by
  have hc : ((-998013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-875316283767/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-998013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c131 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-82263/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4986731/10000000) (δ := 1597/200000000) (ψ := -555919/1000000) 158 123
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t131 : ((-14376466293/400000000000 : ℚ) : ℝ) ≤ stT158 131 := by
  have hc : ((-82273/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14376466293/400000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-82273/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c132 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((701593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -991457/5000000) (δ := 1597/200000000) (ψ := -555919/1000000) 158 123
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t132 : ((152653652171/2500000000000 : ℚ) : ℝ) ≤ stT158 132 := by
  have hc : ((701543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152653652171/2500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((701543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c133 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((115167/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 99823/1000000) (δ := 1597/200000000) (ψ := -555919/1000000) 158 123
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t133 : ((399427691087/5000000000000 : ℚ) : ℝ) ≤ stT158 133 := by
  have hc : ((460643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((399427691087/5000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((460643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c134 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-6009/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3957037/10000000) (δ := 3197/200000000) (ψ := -555919/1000000) 158 123
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t134 : ((-2606292773/2500000000000 : ℚ) : ℝ) ≤ stT158 134 := by
  have hc : ((-3017/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2606292773/2500000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-3017/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c135 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-927153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3446921/5000000) (δ := 1597/200000000) (ψ := -555919/1000000) 158 123
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t135 : ((-798009315589/10000000000000 : ℚ) : ℝ) ≤ stT158 135 := by
  have hc : ((-927203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-798009315589/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-927203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c136 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-354753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2949491/5000000) (δ := 7911/1000000000) (ψ := -555919/1000000) 158 124
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t136 : ((-152109825777/2500000000000 : ℚ) : ℝ) ≤ stT158 136 := by
  have hc : ((-177389/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152109825777/2500000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-177389/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c137 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((360429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -751293/2500000) (δ := 2023/250000000) (ψ := -555919/1000000) 158 124
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t137 : ((307892321303/10000000000000 : ℚ) : ℝ) ≤ stT158 137 := by
  have hc : ((360379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((307892321303/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((360379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c138 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((998597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16557/1250000) (δ := 7911/1000000000) (ψ := -555919/1000000) 158 124
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t138 : ((106252390629/1250000000000 : ℚ) : ℝ) ≤ stT158 138 := by
  have hc : ((998547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106252390629/1250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((998547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c139 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((464413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2719563/10000000) (δ := 2023/250000000) (ψ := -555919/1000000) 158 124
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t139 : ((98466781061/2500000000000 : ℚ) : ℝ) ≤ stT158 139 := by
  have hc : ((464363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98466781061/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((464363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c140 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-604909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69389/125000) (δ := 7911/1000000000) (ψ := -555919/1000000) 158 124
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t140 : ((-102256824729/2000000000000 : ℚ) : ℝ) ≤ stT158 140 := by
  have hc : ((-604959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102256824729/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-604959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c141 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-122423/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -734547/1000000) (δ := 7999/1000000000) (ψ := -555919/1000000) 158 125
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t141 : ((-51552018873/625000000000 : ℚ) : ℝ) ≤ stT158 141 := by
  have hc : ((-489717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51552018873/625000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-489717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c142 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-124077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2276963/5000000) (δ := 7999/1000000000) (ψ := -555919/1000000) 158 125
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t142 : ((-26036041141/1250000000000 : ℚ) : ℝ) ≤ stT158 142 := by
  have hc : ((-62051/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26036041141/1250000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-62051/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c143 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((756541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -890987/5000000) (δ := 7999/1000000000) (ψ := -555919/1000000) 158 125
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t143 : ((316304773411/5000000000000 : ℚ) : ℝ) ≤ stT158 143 := by
  have hc : ((756491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316304773411/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((756491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c144 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((925573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 970623/10000000) (δ := 7999/1000000000) (ψ := -555919/1000000) 158 125
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t144 : ((771268858159/10000000000000 : ℚ) : ℝ) ≤ stT158 144 := by
  have hc : ((925523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((771268858159/10000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((925523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c145 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((8899/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 185211/500000) (δ := 2001/250000000) (ψ := -555919/1000000) 158 125
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t145 : ((1846514469/250000000000 : ℚ) : ℝ) ≤ stT158 145 := by
  have hc : ((4447/50000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1846514469/250000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((4447/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c146 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-839743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 802377/1250000) (δ := 7999/1000000000) (ψ := -555919/1000000) 158 125
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t146 : ((-347508862779/5000000000000 : ℚ) : ℝ) ≤ stT158 146 := by
  have hc : ((-839793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-347508862779/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-839793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c147 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-875413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6592717/10000000) (δ := 3953/500000000) (ψ := -555919/1000000) 158 126
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t147 : ((-722070501381/10000000000000 : ℚ) : ℝ) ≤ stT158 147 := by
  have hc : ((-875463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-722070501381/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-875463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c148 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((2451/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -244671/625000) (δ := 8097/1000000000) (ψ := -555919/1000000) 158 126
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t148 : ((498539361/1250000000000 : ℚ) : ℝ) ≤ stT158 148 := by
  have hc : ((1213/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((498539361/1250000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((1213/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c149 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((876667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -627383/5000000) (δ := 3953/500000000) (ψ := -555919/1000000) 158 126
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t149 : ((718151821527/10000000000000 : ℚ) : ℝ) ≤ stT158 149 := by
  have hc : ((876617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((718151821527/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((876617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c150 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((212483/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1387349/10000000) (δ := 8097/1000000000) (ψ := -555919/1000000) 158 126
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t150 : ((21685164171/312500000000 : ℚ) : ℝ) ≤ stT158 150 := by
  have hc : ((424941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21685164171/312500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((424941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c151 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-531/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2005983/5000000) (δ := 8097/1000000000) (ψ := -555919/1000000) 158 126
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t151 : ((-13848247413/5000000000000 : ℚ) : ℝ) ≤ stT158 151 := by
  have hc : ((-17017/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13848247413/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-17017/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c152 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-880493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6619243/10000000) (δ := 3953/500000000) (ψ := -555919/1000000) 158 126
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t152 : ((-178553867911/2500000000000 : ℚ) : ℝ) ≤ stT158 152 := by
  have hc : ((-880543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178553867911/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-880543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c153 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-856589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6498547/10000000) (δ := 8013/1000000000) (ψ := -555919/1000000) 158 127
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t153 : ((-692552369467/10000000000000 : ℚ) : ℝ) ≤ stT158 153 := by
  have hc : ((-856639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-692552369467/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-856639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c154 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((7/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3925241/10000000) (δ := 799/100000000) (ψ := -555919/1000000) 158 127
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t154 : ((5237843/100000000000 : ℚ) : ℝ) ≤ stT158 154 := by
  have hc : ((13/20000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5237843/100000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((13/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c155 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((853859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1368603/10000000) (δ := 8013/1000000000) (ψ := -555919/1000000) 158 127
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t155 : ((685795611171/10000000000000 : ℚ) : ℝ) ≤ stT158 155 := by
  have hc : ((853809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((685795611171/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((853809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c156 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((892183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 585801/5000000) (δ := 799/100000000) (ψ := -555919/1000000) 158 127
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t156 : ((1116058383/15625000000 : ℚ) : ℝ) ≤ stT158 156 := by
  have hc : ((892133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1116058383/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((892133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c157 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((18487/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3695573/10000000) (δ := 799/100000000) (ψ := -555919/1000000) 158 127
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t157 : ((7373117511/1000000000000 : ℚ) : ℝ) ≤ stT158 157 := by
  have hc : ((18477/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7373117511/1000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((18477/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c158 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-197469/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6203507/10000000) (δ := 799/100000000) (ψ := -555919/1000000) 158 127
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t158 : ((-157107987177/2500000000000 : ℚ) : ℝ) ≤ stT158 158 := by
  have hc : ((-394963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157107987177/2500000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-394963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c159 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-471931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3506161/5000000) (δ := 99/12500000) (ψ := -555919/1000000) 158 128
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t159 : ((-23392853107/312500000000 : ℚ) : ℝ) ≤ stT158 159 := by
  have hc : ((-117989/125000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23392853107/312500000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-117989/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c160 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-48227/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -453583/1000000) (δ := 99/12500000) (ψ := -555919/1000000) 158 128
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t160 : ((-3813472509/200000000000 : ℚ) : ℝ) ≤ stT158 160 := by
  have hc : ((-48237/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3813472509/200000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-48237/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c161 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((33747/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2074783/10000000) (δ := 8083/1000000000) (ψ := -555919/1000000) 158 128
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t161 : ((5318875579/100000000000 : ℚ) : ℝ) ≤ stT158 161 := by
  have hc : ((67489/100000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5318875579/100000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((67489/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c162 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((494503/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 371057/10000000) (δ := 8083/1000000000) (ψ := -555919/1000000) 158 128
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t162 : ((97124627043/1250000000000 : ℚ) : ℝ) ≤ stT158 162 := by
  have hc : ((247239/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97124627043/1250000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((247239/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c163 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((435017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 350231/1250000) (δ := 99/12500000) (ψ := -555919/1000000) 158 128
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t163 : ((17034612621/500000000000 : ℚ) : ℝ) ≤ stT158 163 := by
  have hc : ((434967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17034612621/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((434967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c164 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-123417/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5217747/10000000) (δ := 99/12500000) (ψ := -555919/1000000) 158 128
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t164 : ((-192764540471/5000000000000 : ℚ) : ℝ) ≤ stT158 164 := by
  have hc : ((-246859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192764540471/5000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-246859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c165 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-15556/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 952369/1250000) (δ := 99/12500000) (ψ := -555919/1000000) 158 128
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t165 : ((-387550036683/5000000000000 : ℚ) : ℝ) ≤ stT158 165 := by
  have hc : ((-497817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-387550036683/5000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-497817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c166 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-81491/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5702303/10000000) (δ := 319/40000000) (ψ := -555919/1000000) 158 129
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t166 : ((-253016688339/5000000000000 : ℚ) : ℝ) ≤ stT158 166 := by
  have hc : ((-325989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253016688339/5000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-325989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c167 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((9463/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3329893/10000000) (δ := 2007/250000000) (ψ := -555919/1000000) 158 129
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t167 : ((7321139403/400000000000 : ℚ) : ℝ) ≤ stT158 167 := by
  have hc : ((9461/40000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7321139403/400000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((9461/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c168 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((925409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -121463/1250000) (δ := 319/40000000) (ψ := -555919/1000000) 158 129
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t168 : ((178482318561/2500000000000 : ℚ) : ℝ) ≤ stT158 168 := by
  have hc : ((925359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178482318561/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((925359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c169 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((426519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 686271/5000000) (δ := 319/40000000) (ψ := -555919/1000000) 158 129
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t169 : ((16403598981/250000000000 : ℚ) : ℝ) ≤ stT158 169 := by
  have hc : ((213247/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16403598981/250000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((213247/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c170 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((89507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 925731/2500000) (δ := 2007/250000000) (ψ := -555919/1000000) 158 129
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t170 : ((17152574637/2500000000000 : ℚ) : ℝ) ≤ stT158 170 := by
  have hc : ((89457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17152574637/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((89457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c171 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-742677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3009819/5000000) (δ := 319/40000000) (ψ := -555919/1000000) 158 129
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t171 : ((-7099727393/125000000000 : ℚ) : ℝ) ≤ stT158 171 := by
  have hc : ((-742727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7099727393/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-742727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c172 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-196493/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46157/62500) (δ := 2017/250000000) (ψ := -555919/1000000) 158 130
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t172 : ((-149832161979/2000000000000 : ℚ) : ℝ) ≤ stT158 172 := by
  have hc : ((-196503/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149832161979/2000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-196503/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c173 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-225243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1019053/2000000) (δ := 1587/200000000) (ψ := -555919/1000000) 158 130
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t173 : ((-21408513331/625000000000 : ℚ) : ℝ) ≤ stT158 173 := by
  have hc : ((-56317/125000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21408513331/625000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-56317/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c174 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((107243/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -704651/2500000) (δ := 2017/250000000) (ψ := -555919/1000000) 158 130
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t174 : ((81291227589/2500000000000 : ℚ) : ℝ) ≤ stT158 174 := by
  have hc : ((214461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81291227589/2500000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((214461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c175 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((975461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -554977/10000000) (δ := 1587/200000000) (ψ := -555919/1000000) 158 130
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t175 : ((92167560801/1250000000000 : ℚ) : ℝ) ≤ stT158 175 := by
  have hc : ((975411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92167560801/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((975411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c176 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((155729/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1695733/10000000) (δ := 1587/200000000) (ψ := -555919/1000000) 158 130
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t176 : ((58688778191/1000000000000 : ℚ) : ℝ) ≤ stT158 176 := by
  have hc : ((155719/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58688778191/1000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((155719/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c177 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-2693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 983431/2500000) (δ := 1587/200000000) (ψ := -555919/1000000) 158 130
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t177 : ((-2061767721/10000000000000 : ℚ) : ℝ) ≤ stT158 177 := by
  have hc : ((-2743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2061767721/10000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-2743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c178 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-194713/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 246363/400000) (δ := 1587/200000000) (ψ := -555919/1000000) 158 130
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t178 : ((-72976496733/1250000000000 : ℚ) : ℝ) ≤ stT158 178 := by
  have hc : ((-389451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72976496733/1250000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-389451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c179 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-978611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -366799/500000) (δ := 7961/1000000000) (ψ := -555919/1000000) 158 131
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t179 : ((-182871615799/2500000000000 : ℚ) : ℝ) ≤ stT158 179 := by
  have hc : ((-978661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182871615799/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-978661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c180 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-464773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1027087/2000000) (δ := 7961/1000000000) (ψ := -555919/1000000) 158 131
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t180 : ((-86614652997/2500000000000 : ℚ) : ℝ) ≤ stT158 180 := by
  have hc : ((-464823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86614652997/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-464823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c181 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((382013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -184191/625000) (δ := 7961/1000000000) (ψ := -555919/1000000) 158 131
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t181 : ((141955403061/5000000000000 : ℚ) : ℝ) ≤ stT158 181 := by
  have hc : ((381963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141955403061/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((381963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c182 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((952849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -192691/2500000) (δ := 7961/1000000000) (ψ := -555919/1000000) 158 131
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t182 : ((706261305951/10000000000000 : ℚ) : ℝ) ≤ stT158 182 := by
  have hc : ((952799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((706261305951/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((952799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c183 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((212151/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1393639/10000000) (δ := 4021/500000000) (ψ := -555919/1000000) 158 131
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t183 : ((313634468217/5000000000000 : ℚ) : ℝ) ≤ stT158 183 := by
  have hc : ((424277/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((313634468217/5000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((424277/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c184 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((37929/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3546231/10000000) (δ := 4021/500000000) (ψ := -555919/1000000) 158 131
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t184 : ((55904770097/5000000000000 : ℚ) : ℝ) ≤ stT158 184 := by
  have hc : ((75833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55904770097/5000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((75833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c185 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-647327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 568717/1000000) (δ := 7961/1000000000) (ψ := -555919/1000000) 158 131
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t185 : ((-95192256211/2000000000000 : ℚ) : ℝ) ≤ stT158 185 := by
  have hc : ((-647377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95192256211/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-647377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c186 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-62493/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 977067/1250000) (δ := 7961/1000000000) (ψ := -555919/1000000) 158 131
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t186 : ((-91648817421/1250000000000 : ℚ) : ℝ) ≤ stT158 186 := by
  have hc : ((-499969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91648817421/1250000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-499969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c187 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-673237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5773437/10000000) (δ := 7949/1000000000) (ψ := -555919/1000000) 158 132
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t187 : ((-492356604351/10000000000000 : ℚ) : ℝ) ≤ stT158 187 := by
  have hc : ((-673287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-492356604351/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-673287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c188 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((20779/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -114587/312500) (δ := 4027/500000000) (ψ := -555919/1000000) 158 132
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t188 : ((3786832539/500000000000 : ℚ) : ℝ) ≤ stT158 188 := by
  have hc : ((20769/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3786832539/500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((20769/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c189 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((404453/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1571269/10000000) (δ := 7949/1000000000) (ψ := -555919/1000000) 158 132
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t189 : ((2298263217/39062500000 : ℚ) : ℝ) ≤ stT158 189 := by
  have hc : ((101107/125000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2298263217/39062500000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((101107/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c190 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((15297/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 256573/5000000) (δ := 7949/1000000000) (ψ := -555919/1000000) 158 132
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t190 : ((88776316751/1250000000000 : ℚ) : ℝ) ≤ stT158 190 := by
  have hc : ((489479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88776316751/1250000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((489479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c191 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((102163/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2586659/10000000) (δ := 7949/1000000000) (ψ := -555919/1000000) 158 132
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t191 : ((36957627411/1000000000000 : ℚ) : ℝ) ≤ stT158 191 := by
  have hc : ((102153/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36957627411/1000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((102153/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c192 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-71231/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4649309/10000000) (δ := 4027/500000000) (ψ := -555919/1000000) 158 132
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t192 : ((-12853894757/625000000000 : ℚ) : ℝ) ≤ stT158 192 := by
  have hc : ((-142487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12853894757/625000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-142487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c193 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-55973/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1340251/2000000) (δ := 4027/500000000) (ψ := -555919/1000000) 158 132
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t193 : ((-40292510393/625000000000 : ℚ) : ℝ) ≤ stT158 193 := by
  have hc : ((-447809/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40292510393/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-447809/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c194 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-937489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1741337/2500000) (δ := 7947/1000000000) (ψ := -555919/1000000) 158 133
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t194 : ((-673114562901/10000000000000 : ℚ) : ℝ) ≤ stT158 194 := by
  have hc : ((-937539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-673114562901/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-937539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c195 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-392181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -986899/2000000) (δ := 7947/1000000000) (ψ := -555919/1000000) 158 133
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t195 : ((-56176500513/2000000000000 : ℚ) : ℝ) ≤ stT158 195 := by
  have hc : ((-392231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56176500513/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-392231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c196 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((98547/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -291403/1000000) (δ := 1007/125000000) (ψ := -555919/1000000) 158 133
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t196 : ((28152686133/1000000000000 : ℚ) : ℝ) ≤ stT158 196 := by
  have hc : ((197069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28152686133/1000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((197069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c197 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((187071/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -225959/2500000) (δ := 7947/1000000000) (ψ := -555919/1000000) 158 133
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t197 : ((13327535067/200000000000 : ℚ) : ℝ) ≤ stT158 197 := by
  have hc : ((187061/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13327535067/200000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((187061/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c198 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((905403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 137021/1250000) (δ := 1007/125000000) (ψ := -555919/1000000) 158 133
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t198 : ((643406311157/10000000000000 : ℚ) : ℝ) ≤ stT158 198 := by
  have hc : ((905353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((643406311157/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((905353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c199 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((6601/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3086099/10000000) (δ := 1007/125000000) (ψ := -555919/1000000) 158 133
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t199 : ((23393073/1000000000 : ℚ) : ℝ) ≤ stT158 199 := by
  have hc : ((33/100 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23393073/1000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((33/100 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c200 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-440017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1266509/2500000) (δ := 7947/1000000000) (ψ := -555919/1000000) 158 133
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t200 : ((-311174456169/10000000000000 : ℚ) : ℝ) ≤ stT158 200 := by
  have hc : ((-440067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-311174456169/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-440067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c201 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-473483/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3518069/5000000) (δ := 7947/1000000000) (ψ := -555919/1000000) 158 133
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t201 : ((-41748371721/625000000000 : ℚ) : ℝ) ≤ stT158 201 := by
  have hc : ((-118377/125000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41748371721/625000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-118377/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c202 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-448697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6711559/10000000) (δ := 8039/1000000000) (ψ := -555919/1000000) 158 134
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t202 : ((-78929975439/1250000000000 : ℚ) : ℝ) ≤ stT158 202 := by
  have hc : ((-224361/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78929975439/1250000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-224361/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c203 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-5116/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -476093/1000000) (δ := 1991/250000000) (ψ := -555919/1000000) 158 134
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t203 : ((-114920942031/5000000000000 : ℚ) : ℝ) ≤ stT158 203 := by
  have hc : ((-163737/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114920942031/5000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-163737/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c204 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((53563/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28199/100000) (δ := 1991/250000000) (ψ := -555919/1000000) 158 134
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t204 : ((7499444589/250000000000 : ℚ) : ℝ) ≤ stT158 204 := by
  have hc : ((214227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7499444589/250000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((214227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c205 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((117191/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17767/200000) (δ := 1991/250000000) (ψ := -555919/1000000) 158 134
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t205 : ((32738137977/500000000000 : ℚ) : ℝ) ≤ stT158 205 := by
  have hc : ((468739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32738137977/500000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((468739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c206 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((14308/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1033799/10000000) (δ := 1991/250000000) (ψ := -555919/1000000) 158 134
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t206 : ((318985966123/5000000000000 : ℚ) : ℝ) ≤ stT158 206 := by
  have hc : ((457831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((318985966123/5000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((457831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c207 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((95543/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1473313/5000000) (δ := 1991/250000000) (ψ := -555919/1000000) 158 134
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t207 : ((16599570741/625000000000 : ℚ) : ℝ) ≤ stT158 207 := by
  have hc : ((191061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16599570741/625000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((191061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c208 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-180483/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4850249/10000000) (δ := 8039/1000000000) (ψ := -555919/1000000) 158 134
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t208 : ((-244452959/9765625000 : ℚ) : ℝ) ≤ stT158 208 := by
  have hc : ((-45127/125000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244452959/9765625000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-45127/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c209 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-225793/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1686187/2500000) (δ := 8039/1000000000) (ψ := -555919/1000000) 158 134
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t209 : ((-62477220573/1000000000000 : ℚ) : ℝ) ≤ stT158 209 := by
  have hc : ((-451611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62477220573/1000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-451611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c210 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-190437/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7077761/10000000) (δ := 8071/1000000000) (ψ := -555919/1000000) 158 135
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t210 : ((-65710499751/1000000000000 : ℚ) : ℝ) ≤ stT158 210 := by
  have hc : ((-190447/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65710499751/1000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-190447/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c211 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-487927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2600637/5000000) (δ := 8071/1000000000) (ψ := -555919/1000000) 158 135
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t211 : ((-335937518133/10000000000000 : ℚ) : ℝ) ≤ stT158 211 := by
  have hc : ((-487977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-335937518133/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-487977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c212 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((47021/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -133347/400000) (δ := 1983/250000000) (ψ := -555919/1000000) 158 135
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t212 : ((16143624411/1000000000000 : ℚ) : ℝ) ≤ stT158 212 := by
  have hc : ((47011/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16143624411/1000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((47011/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c213 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((33239/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -368711/2500000) (δ := 8071/1000000000) (ψ := -555919/1000000) 158 135
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t213 : ((5693398389/100000000000 : ℚ) : ℝ) ≤ stT158 213 := by
  have hc : ((33237/40000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5693398389/100000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((33237/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c214 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((988753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2932/78125) (δ := 1983/250000000) (ψ := -555919/1000000) 158 135
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t214 : ((135172508051/2000000000000 : ℚ) : ℝ) ≤ stT158 214 := by
  have hc : ((988703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135172508051/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((988703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c215 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((315981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1108393/5000000) (δ := 1983/250000000) (ψ := -555919/1000000) 158 135
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t215 : ((26935012033/625000000000 : ℚ) : ℝ) ≤ stT158 215 := by
  have hc : ((78989/125000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26935012033/625000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((78989/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c216 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-24541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 253109/625000) (δ := 1983/250000000) (ψ := -555919/1000000) 158 135
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t216 : ((-4178762581/1250000000000 : ℚ) : ℝ) ≤ stT158 216 := by
  have hc : ((-12283/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4178762581/1250000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-12283/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c217 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-87811/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 587421/1000000) (δ := 8071/1000000000) (ψ := -555919/1000000) 158 135
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t217 : ((-47691440861/1000000000000 : ℚ) : ℝ) ≤ stT158 217 := by
  have hc : ((-351269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47691440861/1000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-351269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c218 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-997857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7690301/10000000) (δ := 1983/250000000) (ψ := -555919/1000000) 158 135
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t218 : ((-337934220201/5000000000000 : ℚ) : ℝ) ≤ stT158 218 := by
  have hc : ((-997907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-337934220201/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-997907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c219 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-791433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3104933/5000000) (δ := 321/40000000) (ψ := -555919/1000000) 158 136
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t219 : ((-267417569727/5000000000000 : ℚ) : ℝ) ≤ stT158 219 := by
  have hc : ((-791483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-267417569727/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-791483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c220 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-48033/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -176413/400000) (δ := 321/40000000) (ψ := -555919/1000000) 158 136
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t220 : ((-323922761/25000000000 : ℚ) : ℝ) ≤ stT158 220 := by
  have hc : ((-96091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-323922761/25000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-96091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c221 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((499679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2618921/10000000) (δ := 321/40000000) (ψ := -555919/1000000) 158 136
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t221 : ((10502701209/312500000000 : ℚ) : ℝ) ≤ stT158 221 := by
  have hc : ((499629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10502701209/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((499629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c222 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((944653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -417827/5000000) (δ := 321/40000000) (ψ := -555919/1000000) 158 136
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t222 : ((158493992767/2500000000000 : ℚ) : ℝ) ≤ stT158 222 := by
  have hc : ((944603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158493992767/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((944603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c223 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((186039/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 469817/5000000) (δ := 321/40000000) (ψ := -555919/1000000) 158 136
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t223 : ((124574133821/2000000000000 : ℚ) : ℝ) ≤ stT158 223 := by
  have hc : ((186029/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124574133821/2000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((186029/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c224 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((468863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2706983/10000000) (δ := 3989/500000000) (ψ := -555919/1000000) 158 136
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t224 : ((313238812389/10000000000000 : ℚ) : ℝ) ≤ stT158 224 := by
  have hc : ((468813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((313238812389/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((468813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c225 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-214121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4466471/10000000) (δ := 3989/500000000) (ψ := -555919/1000000) 158 136
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t225 : ((-142780738057/10000000000000 : ℚ) : ℝ) ≤ stT158 225 := by
  have hc : ((-214171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142780738057/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-214171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c226 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-396723/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3109059/5000000) (δ := 633/40000000) (ψ := -555919/1000000) 158 136
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t226 : ((-65978299717/1250000000000 : ℚ) : ℝ) ≤ stT158 226 := by
  have hc : ((-99187/125000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65978299717/1250000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-99187/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c227 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-499533/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -77459/100000) (δ := 1617/200000000) (ψ := -555919/1000000) 158 137
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t227 : ((-41446079249/625000000000 : ℚ) : ℝ) ≤ stT158 227 := by
  have hc : ((-249779/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41446079249/625000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-249779/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c228 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-92499/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3004819/5000000) (δ := 1617/200000000) (ψ := -555919/1000000) 158 137
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t228 : ((-245052697607/5000000000000 : ℚ) : ℝ) ≤ stT158 228 := by
  have hc : ((-370021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245052697607/5000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-370021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c229 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-28223/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6689/15625) (δ := 1617/200000000) (ψ := -555919/1000000) 158 137
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t229 : ((-18656902827/2000000000000 : ℚ) : ℝ) ≤ stT158 229 := by
  have hc : ((-28233/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18656902827/2000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-28233/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c230 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((130003/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2559827/10000000) (δ := 3959/500000000) (ψ := -555919/1000000) 158 137
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t230 : ((8571313589/250000000000 : ℚ) : ℝ) ≤ stT158 230 := by
  have hc : ((259981/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8571313589/250000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((259981/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c231 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((471633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -846159/10000000) (δ := 3959/500000000) (ψ := -555919/1000000) 158 137
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t231 : ((38786869401/625000000000 : ℚ) : ℝ) ≤ stT158 231 := by
  have hc : ((58951/62500 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38786869401/625000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((58951/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c232 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((470701/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 860083/10000000) (δ := 3959/500000000) (ψ := -555919/1000000) 158 137
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t232 : ((19313365977/312500000000 : ℚ) : ℝ) ≤ stT158 232 := by
  have hc : ((117669/125000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19313365977/312500000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((117669/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c233 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((520289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1279509/5000000) (δ := 1617/200000000) (ψ := -555919/1000000) 158 137
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t233 : ((340819493919/10000000000000 : ℚ) : ℝ) ≤ stT158 233 := by
  have hc : ((520239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((340819493919/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((520239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c234 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-32279/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1062671/2500000) (δ := 3959/500000000) (ψ := -555919/1000000) 158 137
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t234 : ((-42219263343/5000000000000 : ℚ) : ℝ) ≤ stT158 234 := by
  have hc : ((-64583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42219263343/5000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-64583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c235 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-359809/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2967561/5000000) (δ := 3959/500000000) (ψ := -555919/1000000) 158 137
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t235 : ((-117365076693/2500000000000 : ℚ) : ℝ) ≤ stT158 235 := by
  have hc : ((-179917/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117365076693/2500000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-179917/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c236 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-199067/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7612411/10000000) (δ := 1617/200000000) (ψ := -555919/1000000) 158 137
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t236 : ((-25917635553/400000000000 : ℚ) : ℝ) ≤ stT158 236 := by
  have hc : ((-199077/200000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25917635553/400000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-199077/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c237 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-841121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3212687/5000000) (δ := 999/125000000) (ψ := -555919/1000000) 158 138
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t237 : ((-54639944647/1000000000000 : ℚ) : ℝ) ≤ stT158 237 := by
  have hc : ((-841171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54639944647/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-841171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c238 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-163957/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4762227/10000000) (δ := 8011/1000000000) (ψ := -555919/1000000) 158 138
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t238 : ((-13286723541/625000000000 : ℚ) : ℝ) ≤ stT158 238 := by
  have hc : ((-81991/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13286723541/625000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-81991/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c239 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((161257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3106031/10000000) (δ := 999/125000000) (ψ := -555919/1000000) 158 138
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t239 : ((3259133571/156250000000 : ℚ) : ℝ) ≤ stT158 239 := by
  have hc : ((10077/31250 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3259133571/156250000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((10077/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c240 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((41749/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -364187/2500000) (δ := 999/125000000) (ψ := -555919/1000000) 158 138
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t240 : ((53894481021/1000000000000 : ℚ) : ℝ) ≤ stT158 240 := by
  have hc : ((83493/100000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53894481021/1000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((83493/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c241 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((249311/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 92831/5000000) (δ := 999/125000000) (ψ := -555919/1000000) 158 138
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t241 : ((80293562283/1250000000000 : ℚ) : ℝ) ≤ stT158 241 := by
  have hc : ((498597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80293562283/1250000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((498597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c242 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((373083/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 910639/5000000) (δ := 999/125000000) (ψ := -555919/1000000) 158 138
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t242 : ((14988164737/312500000000 : ℚ) : ℝ) ≤ stT158 242 := by
  have hc : ((186529/250000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14988164737/312500000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((186529/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c243 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((94793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3450139/10000000) (δ := 8011/1000000000) (ψ := -555919/1000000) 158 138
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t243 : ((7599209/625000000 : ℚ) : ℝ) ≤ stT158 243 := by
  have hc : ((5923/31250 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7599209/625000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((5923/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c244 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-17691/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 202893/400000) (δ := 8011/1000000000) (ψ := -555919/1000000) 158 138
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t244 : ((-2265358641/80000000000 : ℚ) : ℝ) ≤ stT158 244 := by
  have hc : ((-17693/40000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2265358641/80000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-17693/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c245 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-89317/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 417991/625000) (δ := 1999/125000000) (ψ := -555919/1000000) 158 138
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t245 : ((-28532885697/500000000000 : ℚ) : ℝ) ≤ stT158 245 := by
  have hc : ((-44661/50000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28532885697/500000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-44661/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c246 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-30761/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3705567/5000000) (δ := 8099/1000000000) (ψ := -555919/1000000) 158 139
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t246 : ((-313816036977/5000000000000 : ℚ) : ℝ) ≤ stT158 246 := by
  have hc : ((-492201/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-313816036977/5000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-492201/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c247 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-683599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2904349/5000000) (δ := 8099/1000000000) (ψ := -555919/1000000) 158 139
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t247 : ((-86999120793/2000000000000 : ℚ) : ℝ) ≤ stT158 247 := by
  have hc : ((-683649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86999120793/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-683649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c248 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-114051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -210637/500000) (δ := 8099/1000000000) (ψ := -555919/1000000) 158 139
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t248 : ((-72454249101/10000000000000 : ℚ) : ℝ) ≤ stT158 248 := by
  have hc : ((-114101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72454249101/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-114101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c249 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((124547/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2623221/10000000) (δ := 247/31250000) (ψ := -555919/1000000) 158 139
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t249 : ((39460250739/1250000000000 : ℚ) : ℝ) ≤ stT158 249 := by
  have hc : ((249069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39460250739/1250000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((249069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_c250 :
    |Real.cos (((158 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((914709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1040021/10000000) (δ := 8099/1000000000) (ψ := -555919/1000000) 158 139
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st158_t250 : ((115696131569/2000000000000 : ℚ) : ℝ) ≤ stT158 250 := by
  have hc : ((914659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((158 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st158_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115696131569/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((914659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st158_p1 : ((424683/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT158 (i+1) := by
  rw [Finset.sum_range_one]
  exact st158_t1

theorem st158_p2 : ((91933113803/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT158 (i+1))
      = (∑ i ∈ Finset.range 1, stT158 (i+1)) + stT158 2 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 1
    simpa using h
  have hprev := st158_p1
  have hstep := st158_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p3 : ((200903498423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT158 (i+1))
      = (∑ i ∈ Finset.range 2, stT158 (i+1)) + stT158 3 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 2
    simpa using h
  have hprev := st158_p2
  have hstep := st158_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p4 : ((4945163498423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT158 (i+1))
      = (∑ i ∈ Finset.range 3, stT158 (i+1)) + stT158 4 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 3
    simpa using h
  have hprev := st158_p3
  have hstep := st158_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p5 : ((788697690119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT158 (i+1))
      = (∑ i ∈ Finset.range 4, stT158 (i+1)) + stT158 5 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 4
    simpa using h
  have hprev := st158_p4
  have hstep := st158_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p6 : ((658450239849/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT158 (i+1))
      = (∑ i ∈ Finset.range 5, stT158 (i+1)) + stT158 6 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 5
    simpa using h
  have hprev := st158_p5
  have hstep := st158_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p7 : ((7038003131497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT158 (i+1))
      = (∑ i ∈ Finset.range 6, stT158 (i+1)) + stT158 7 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 6
    simpa using h
  have hprev := st158_p6
  have hstep := st158_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p8 : ((4474033874697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT158 (i+1))
      = (∑ i ∈ Finset.range 7, stT158 (i+1)) + stT158 8 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 7
    simpa using h
  have hprev := st158_p7
  have hstep := st158_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p9 : ((534228036157/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT158 (i+1))
      = (∑ i ∈ Finset.range 8, stT158 (i+1)) + stT158 9 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 8
    simpa using h
  have hprev := st158_p8
  have hstep := st158_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p10 : ((1456873558991/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT158 (i+1))
      = (∑ i ∈ Finset.range 9, stT158 (i+1)) + stT158 10 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 9
    simpa using h
  have hprev := st158_p9
  have hstep := st158_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p11 : ((884876282051/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT158 (i+1))
      = (∑ i ∈ Finset.range 10, stT158 (i+1)) + stT158 11 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 10
    simpa using h
  have hprev := st158_p10
  have hstep := st158_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p12 : ((242089709403/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT158 (i+1))
      = (∑ i ∈ Finset.range 11, stT158 (i+1)) + stT158 12 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 11
    simpa using h
  have hprev := st158_p11
  have hstep := st158_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p13 : ((-174084773459/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT158 (i+1))
      = (∑ i ∈ Finset.range 12, stT158 (i+1)) + stT158 13 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 12
    simpa using h
  have hprev := st158_p12
  have hstep := st158_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p14 : ((-246387582709/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT158 (i+1))
      = (∑ i ∈ Finset.range 13, stT158 (i+1)) + stT158 14 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 13
    simpa using h
  have hprev := st158_p13
  have hstep := st158_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p15 : ((-146897758233/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT158 (i+1))
      = (∑ i ∈ Finset.range 14, stT158 (i+1)) + stT158 15 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 14
    simpa using h
  have hprev := st158_p14
  have hstep := st158_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p16 : ((-101379883233/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT158 (i+1))
      = (∑ i ∈ Finset.range 15, stT158 (i+1)) + stT158 16 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 15
    simpa using h
  have hprev := st158_p15
  have hstep := st158_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p17 : ((-811713433211/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT158 (i+1))
      = (∑ i ∈ Finset.range 16, stT158 (i+1)) + stT158 17 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 16
    simpa using h
  have hprev := st158_p16
  have hstep := st158_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p18 : ((-1467294193609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT158 (i+1))
      = (∑ i ∈ Finset.range 17, stT158 (i+1)) + stT158 18 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 17
    simpa using h
  have hprev := st158_p17
  have hstep := st158_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p19 : ((-274440187933/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT158 (i+1))
      = (∑ i ∈ Finset.range 18, stT158 (i+1)) + stT158 19 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 18
    simpa using h
  have hprev := st158_p18
  have hstep := st158_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p20 : ((-3335851011293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT158 (i+1))
      = (∑ i ∈ Finset.range 19, stT158 (i+1)) + stT158 20 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 19
    simpa using h
  have hprev := st158_p19
  have hstep := st158_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p21 : ((-4646149120559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT158 (i+1))
      = (∑ i ∈ Finset.range 20, stT158 (i+1)) + stT158 21 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 20
    simpa using h
  have hprev := st158_p20
  have hstep := st158_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p22 : ((-1885566469813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT158 (i+1))
      = (∑ i ∈ Finset.range 21, stT158 (i+1)) + stT158 22 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 21
    simpa using h
  have hprev := st158_p21
  have hstep := st158_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p23 : ((-928471820377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT158 (i+1))
      = (∑ i ∈ Finset.range 22, stT158 (i+1)) + stT158 23 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 22
    simpa using h
  have hprev := st158_p22
  have hstep := st158_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p24 : ((183041996031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT158 (i+1))
      = (∑ i ∈ Finset.range 23, stT158 (i+1)) + stT158 24 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 23
    simpa using h
  have hprev := st158_p23
  have hstep := st158_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p25 : ((2142957996031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT158 (i+1))
      = (∑ i ∈ Finset.range 24, stT158 (i+1)) + stT158 25 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 24
    simpa using h
  have hprev := st158_p24
  have hstep := st158_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p26 : ((1022823741063/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT158 (i+1))
      = (∑ i ∈ Finset.range 25, stT158 (i+1)) + stT158 26 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 25
    simpa using h
  have hprev := st158_p25
  have hstep := st158_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p27 : ((1493728683813/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT158 (i+1))
      = (∑ i ∈ Finset.range 26, stT158 (i+1)) + stT158 27 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 26
    simpa using h
  have hprev := st158_p26
  have hstep := st158_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p28 : ((57548007789/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT158 (i+1))
      = (∑ i ∈ Finset.range 27, stT158 (i+1)) + stT158 28 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 27
    simpa using h
  have hprev := st158_p27
  have hstep := st158_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p29 : ((3765281664759/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT158 (i+1))
      = (∑ i ∈ Finset.range 28, stT158 (i+1)) + stT158 29 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 28
    simpa using h
  have hprev := st158_p28
  have hstep := st158_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p30 : ((1543334441083/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT158 (i+1))
      = (∑ i ∈ Finset.range 29, stT158 (i+1)) + stT158 30 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 29
    simpa using h
  have hprev := st158_p29
  have hstep := st158_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p31 : ((449849406063/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT158 (i+1))
      = (∑ i ∈ Finset.range 30, stT158 (i+1)) + stT158 31 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 30
    simpa using h
  have hprev := st158_p30
  have hstep := st158_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p32 : ((2307249200541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT158 (i+1))
      = (∑ i ∈ Finset.range 31, stT158 (i+1)) + stT158 32 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 31
    simpa using h
  have hprev := st158_p31
  have hstep := st158_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p33 : ((3174538619261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT158 (i+1))
      = (∑ i ∈ Finset.range 32, stT158 (i+1)) + stT158 33 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 32
    simpa using h
  have hprev := st158_p32
  have hstep := st158_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p34 : ((1625010127033/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT158 (i+1))
      = (∑ i ∈ Finset.range 33, stT158 (i+1)) + stT158 34 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 33
    simpa using h
  have hprev := st158_p33
  have hstep := st158_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p35 : ((2405648367133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT158 (i+1))
      = (∑ i ∈ Finset.range 34, stT158 (i+1)) + stT158 35 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 34
    simpa using h
  have hprev := st158_p34
  have hstep := st158_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p36 : ((2656296600207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT158 (i+1))
      = (∑ i ∈ Finset.range 35, stT158 (i+1)) + stT158 36 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 35
    simpa using h
  have hprev := st158_p35
  have hstep := st158_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p37 : ((6581573513613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT158 (i+1))
      = (∑ i ∈ Finset.range 36, stT158 (i+1)) + stT158 37 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 36
    simpa using h
  have hprev := st158_p36
  have hstep := st158_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p38 : ((5076855546063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT158 (i+1))
      = (∑ i ∈ Finset.range 37, stT158 (i+1)) + stT158 38 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 37
    simpa using h
  have hprev := st158_p37
  have hstep := st158_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p39 : ((5434319111379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT158 (i+1))
      = (∑ i ∈ Finset.range 38, stT158 (i+1)) + stT158 39 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 38
    simpa using h
  have hprev := st158_p38
  have hstep := st158_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p40 : ((254805700641/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT158 (i+1))
      = (∑ i ∈ Finset.range 39, stT158 (i+1)) + stT158 40 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 39
    simpa using h
  have hprev := st158_p39
  have hstep := st158_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p41 : ((4832870703533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT158 (i+1))
      = (∑ i ∈ Finset.range 40, stT158 (i+1)) + stT158 41 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 40
    simpa using h
  have hprev := st158_p40
  have hstep := st158_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p42 : ((309774537107/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT158 (i+1))
      = (∑ i ∈ Finset.range 41, stT158 (i+1)) + stT158 42 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 41
    simpa using h
  have hprev := st158_p41
  have hstep := st158_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p43 : ((1363981857909/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT158 (i+1))
      = (∑ i ∈ Finset.range 42, stT158 (i+1)) + stT158 43 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 42
    simpa using h
  have hprev := st158_p42
  have hstep := st158_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p44 : ((1369810823183/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT158 (i+1))
      = (∑ i ∈ Finset.range 43, stT158 (i+1)) + stT158 44 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 43
    simpa using h
  have hprev := st158_p43
  have hstep := st158_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p45 : ((6050869842081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT158 (i+1))
      = (∑ i ∈ Finset.range 44, stT158 (i+1)) + stT158 45 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 44
    simpa using h
  have hprev := st158_p44
  have hstep := st158_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p46 : ((5073423744961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT158 (i+1))
      = (∑ i ∈ Finset.range 45, stT158 (i+1)) + stT158 46 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 45
    simpa using h
  have hprev := st158_p45
  have hstep := st158_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p47 : ((6285622327219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT158 (i+1))
      = (∑ i ∈ Finset.range 46, stT158 (i+1)) + stT158 47 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 46
    simpa using h
  have hprev := st158_p46
  have hstep := st158_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p48 : ((991774510279/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT158 (i+1))
      = (∑ i ∈ Finset.range 47, stT158 (i+1)) + stT158 48 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 47
    simpa using h
  have hprev := st158_p47
  have hstep := st158_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p49 : ((3164136784573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT158 (i+1))
      = (∑ i ∈ Finset.range 48, stT158 (i+1)) + stT158 49 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 48
    simpa using h
  have hprev := st158_p48
  have hstep := st158_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p50 : ((2476958888261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT158 (i+1))
      = (∑ i ∈ Finset.range 49, stT158 (i+1)) + stT158 50 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 49
    simpa using h
  have hprev := st158_p49
  have hstep := st158_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p51 : ((3155129195201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT158 (i+1))
      = (∑ i ∈ Finset.range 50, stT158 (i+1)) + stT158 51 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 50
    simpa using h
  have hprev := st158_p50
  have hstep := st158_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p52 : ((1248953840261/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT158 (i+1))
      = (∑ i ∈ Finset.range 51, stT158 (i+1)) + stT158 52 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 51
    simpa using h
  have hprev := st158_p51
  have hstep := st158_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p53 : ((3114352758817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT158 (i+1))
      = (∑ i ∈ Finset.range 52, stT158 (i+1)) + stT158 53 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 52
    simpa using h
  have hprev := st158_p52
  have hstep := st158_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p54 : ((2570487642407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT158 (i+1))
      = (∑ i ∈ Finset.range 53, stT158 (i+1)) + stT158 54 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 53
    simpa using h
  have hprev := st158_p53
  have hstep := st158_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p55 : ((5992579596047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT158 (i+1))
      = (∑ i ∈ Finset.range 54, stT158 (i+1)) + stT158 55 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 54
    simpa using h
  have hprev := st158_p54
  have hstep := st158_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p56 : ((2742870534083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT158 (i+1))
      = (∑ i ∈ Finset.range 55, stT158 (i+1)) + stT158 56 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 55
    simpa using h
  have hprev := st158_p55
  have hstep := st158_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p57 : ((554381782277/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT158 (i+1))
      = (∑ i ∈ Finset.range 56, stT158 (i+1)) + stT158 57 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 56
    simpa using h
  have hprev := st158_p56
  have hstep := st158_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p58 : ((2996861722801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT158 (i+1))
      = (∑ i ∈ Finset.range 57, stT158 (i+1)) + stT158 58 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 57
    simpa using h
  have hprev := st158_p57
  have hstep := st158_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p59 : ((1267110069783/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT158 (i+1))
      = (∑ i ∈ Finset.range 58, stT158 (i+1)) + stT158 59 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 58
    simpa using h
  have hprev := st158_p58
  have hstep := st158_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p60 : ((1575968765337/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT158 (i+1))
      = (∑ i ∈ Finset.range 59, stT158 (i+1)) + stT158 60 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 59
    simpa using h
  have hprev := st158_p59
  have hstep := st158_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p61 : ((5058840404641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT158 (i+1))
      = (∑ i ∈ Finset.range 60, stT158 (i+1)) + stT158 61 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 60
    simpa using h
  have hprev := st158_p60
  have hstep := st158_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p62 : ((2968081722723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT158 (i+1))
      = (∑ i ∈ Finset.range 61, stT158 (i+1)) + stT158 62 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 61
    simpa using h
  have hprev := st158_p61
  have hstep := st158_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p63 : ((359305990303/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT158 (i+1))
      = (∑ i ∈ Finset.range 62, stT158 (i+1)) + stT158 63 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 62
    simpa using h
  have hprev := st158_p62
  have hstep := st158_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p64 : ((5144926611673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT158 (i+1))
      = (∑ i ∈ Finset.range 63, stT158 (i+1)) + stT158 64 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 63
    simpa using h
  have hprev := st158_p63
  have hstep := st158_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p65 : ((3149588702681/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT158 (i+1))
      = (∑ i ∈ Finset.range 64, stT158 (i+1)) + stT158 65 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 64
    simpa using h
  have hprev := st158_p64
  have hstep := st158_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p66 : ((2572407735521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT158 (i+1))
      = (∑ i ∈ Finset.range 65, stT158 (i+1)) + stT158 66 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 65
    simpa using h
  have hprev := st158_p65
  have hstep := st158_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p67 : ((2838355858993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT158 (i+1))
      = (∑ i ∈ Finset.range 66, stT158 (i+1)) + stT158 67 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 66
    simpa using h
  have hprev := st158_p66
  have hstep := st158_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p68 : ((190400370523/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT158 (i+1))
      = (∑ i ∈ Finset.range 67, stT158 (i+1)) + stT158 68 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 67
    simpa using h
  have hprev := st158_p67
  have hstep := st158_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p69 : ((99545021979/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT158 (i+1))
      = (∑ i ∈ Finset.range 68, stT158 (i+1)) + stT158 69 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 68
    simpa using h
  have hprev := st158_p68
  have hstep := st158_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p70 : ((3017940635871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT158 (i+1))
      = (∑ i ∈ Finset.range 69, stT158 (i+1)) + stT158 70 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 69
    simpa using h
  have hprev := st158_p69
  have hstep := st158_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p71 : ((145358883921/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT158 (i+1))
      = (∑ i ∈ Finset.range 70, stT158 (i+1)) + stT158 71 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 70
    simpa using h
  have hprev := st158_p70
  have hstep := st158_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p72 : ((5016125609/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT158 (i+1))
      = (∑ i ∈ Finset.range 71, stT158 (i+1)) + stT158 72 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 71
    simpa using h
  have hprev := st158_p71
  have hstep := st158_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p73 : ((771968762653/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT158 (i+1))
      = (∑ i ∈ Finset.range 72, stT158 (i+1)) + stT158 73 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 72
    simpa using h
  have hprev := st158_p72
  have hstep := st158_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p74 : ((283849350971/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT158 (i+1))
      = (∑ i ∈ Finset.range 73, stT158 (i+1)) + stT158 74 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 73
    simpa using h
  have hprev := st158_p73
  have hstep := st158_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p75 : ((126167048289/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT158 (i+1))
      = (∑ i ∈ Finset.range 74, stT158 (i+1)) + stT158 75 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 74
    simpa using h
  have hprev := st158_p74
  have hstep := st158_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p76 : ((619194181293/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT158 (i+1))
      = (∑ i ∈ Finset.range 75, stT158 (i+1)) + stT158 76 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 75
    simpa using h
  have hprev := st158_p75
  have hstep := st158_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p77 : ((2853661041109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT158 (i+1))
      = (∑ i ∈ Finset.range 76, stT158 (i+1)) + stT158 77 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 76
    simpa using h
  have hprev := st158_p76
  have hstep := st158_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p78 : ((2504884316491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT158 (i+1))
      = (∑ i ∈ Finset.range 77, stT158 (i+1)) + stT158 78 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 77
    simpa using h
  have hprev := st158_p77
  have hstep := st158_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p79 : ((305363087461/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT158 (i+1))
      = (∑ i ∈ Finset.range 78, stT158 (i+1)) + stT158 79 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 78
    simpa using h
  have hprev := st158_p78
  have hstep := st158_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p80 : ((2945311827571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT158 (i+1))
      = (∑ i ∈ Finset.range 79, stT158 (i+1)) + stT158 80 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 79
    simpa using h
  have hprev := st158_p79
  have hstep := st158_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p81 : ((2482696457479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT158 (i+1))
      = (∑ i ∈ Finset.range 80, stT158 (i+1)) + stT158 81 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 80
    simpa using h
  have hprev := st158_p80
  have hstep := st158_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p82 : ((5866669663373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT158 (i+1))
      = (∑ i ∈ Finset.range 81, stT158 (i+1)) + stT158 82 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 81
    simpa using h
  have hprev := st158_p81
  have hstep := st158_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p83 : ((1232221547861/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT158 (i+1))
      = (∑ i ∈ Finset.range 82, stT158 (i+1)) + stT158 83 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 82
    simpa using h
  have hprev := st158_p82
  have hstep := st158_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p84 : ((1014263227281/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT158 (i+1))
      = (∑ i ∈ Finset.range 83, stT158 (i+1)) + stT158 84 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 83
    simpa using h
  have hprev := st158_p83
  have hstep := st158_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p85 : ((1088404614741/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT158 (i+1))
      = (∑ i ∈ Finset.range 84, stT158 (i+1)) + stT158 85 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 84
    simpa using h
  have hprev := st158_p84
  have hstep := st158_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p86 : ((252632089003/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT158 (i+1))
      = (∑ i ∈ Finset.range 85, stT158 (i+1)) + stT158 86 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 85
    simpa using h
  have hprev := st158_p85
  have hstep := st158_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p87 : ((1097632630493/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT158 (i+1))
      = (∑ i ∈ Finset.range 86, stT158 (i+1)) + stT158 87 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 86
    simpa using h
  have hprev := st158_p86
  have hstep := st158_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p88 : ((5020596742001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT158 (i+1))
      = (∑ i ∈ Finset.range 87, stT158 (i+1)) + stT158 88 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 87
    simpa using h
  have hprev := st158_p87
  have hstep := st158_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p89 : ((1210058109553/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT158 (i+1))
      = (∑ i ∈ Finset.range 88, stT158 (i+1)) + stT158 89 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 88
    simpa using h
  have hprev := st158_p88
  have hstep := st158_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p90 : ((6097542329849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT158 (i+1))
      = (∑ i ∈ Finset.range 89, stT158 (i+1)) + stT158 90 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 89
    simpa using h
  have hprev := st158_p89
  have hstep := st158_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p91 : ((5058075503269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT158 (i+1))
      = (∑ i ∈ Finset.range 90, stT158 (i+1)) + stT158 91 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 90
    simpa using h
  have hprev := st158_p90
  have hstep := st158_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p92 : ((5352332067121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT158 (i+1))
      = (∑ i ∈ Finset.range 91, stT158 (i+1)) + stT158 92 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 91
    simpa using h
  have hprev := st158_p91
  have hstep := st158_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p93 : ((3148809854787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT158 (i+1))
      = (∑ i ∈ Finset.range 92, stT158 (i+1)) + stT158 93 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 92
    simpa using h
  have hprev := st158_p92
  have hstep := st158_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p94 : ((288250339863/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT158 (i+1))
      = (∑ i ∈ Finset.range 93, stT158 (i+1)) + stT158 94 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 93
    simpa using h
  have hprev := st158_p93
  have hstep := st158_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p95 : ((988864213053/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT158 (i+1))
      = (∑ i ∈ Finset.range 94, stT158 (i+1)) + stT158 95 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 94
    simpa using h
  have hprev := st158_p94
  have hstep := st158_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p96 : ((1124584015289/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT158 (i+1))
      = (∑ i ∈ Finset.range 95, stT158 (i+1)) + stT158 96 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 95
    simpa using h
  have hprev := st158_p95
  have hstep := st158_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p97 : ((6334669499677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT158 (i+1))
      = (∑ i ∈ Finset.range 96, stT158 (i+1)) + stT158 97 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 96
    simpa using h
  have hprev := st158_p96
  have hstep := st158_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p98 : ((1394986704429/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT158 (i+1))
      = (∑ i ∈ Finset.range 97, stT158 (i+1)) + stT158 98 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 97
    simpa using h
  have hprev := st158_p97
  have hstep := st158_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p99 : ((493717777993/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT158 (i+1))
      = (∑ i ∈ Finset.range 98, stT158 (i+1)) + stT158 99 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 98
    simpa using h
  have hprev := st158_p98
  have hstep := st158_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p100 : ((1429193750083/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT158 (i+1))
      = (∑ i ∈ Finset.range 99, stT158 (i+1)) + stT158 100 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 99
    simpa using h
  have hprev := st158_p99
  have hstep := st158_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p101 : ((3169387309553/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT158 (i+1))
      = (∑ i ∈ Finset.range 100, stT158 (i+1)) + stT158 101 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 100
    simpa using h
  have hprev := st158_p100
  have hstep := st158_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p102 : ((2787368408193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT158 (i+1))
      = (∑ i ∈ Finset.range 101, stT158 (i+1)) + stT158 102 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 101
    simpa using h
  have hprev := st158_p101
  have hstep := st158_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p103 : ((2462935696403/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT158 (i+1))
      = (∑ i ∈ Finset.range 102, stT158 (i+1)) + stT158 103 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 102
    simpa using h
  have hprev := st158_p102
  have hstep := st158_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p104 : ((2817273672593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT158 (i+1))
      = (∑ i ∈ Finset.range 103, stT158 (i+1)) + stT158 104 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 103
    simpa using h
  have hprev := st158_p103
  have hstep := st158_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p105 : ((3174617999693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT158 (i+1))
      = (∑ i ∈ Finset.range 104, stT158 (i+1)) + stT158 105 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 104
    simpa using h
  have hprev := st158_p104
  have hstep := st158_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p106 : ((287080896611/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT158 (i+1))
      = (∑ i ∈ Finset.range 105, stT158 (i+1)) + stT158 106 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 105
    simpa using h
  have hprev := st158_p105
  have hstep := st158_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p107 : ((4937517997941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT158 (i+1))
      = (∑ i ∈ Finset.range 106, stT158 (i+1)) + stT158 107 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 106
    simpa using h
  have hprev := st158_p106
  have hstep := st158_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p108 : ((5388279199191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT158 (i+1))
      = (∑ i ∈ Finset.range 107, stT158 (i+1)) + stT158 108 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 107
    simpa using h
  have hprev := st158_p107
  have hstep := st158_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p109 : ((6280190487349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT158 (i+1))
      = (∑ i ∈ Finset.range 108, stT158 (i+1)) + stT158 109 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 108
    simpa using h
  have hprev := st158_p108
  have hstep := st158_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p110 : ((604873448371/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT158 (i+1))
      = (∑ i ∈ Finset.range 109, stT158 (i+1)) + stT158 110 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 109
    simpa using h
  have hprev := st158_p109
  have hstep := st158_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p111 : ((2552340527717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT158 (i+1))
      = (∑ i ∈ Finset.range 110, stT158 (i+1)) + stT158 111 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 110
    simpa using h
  have hprev := st158_p110
  have hstep := st158_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p112 : ((2528931277829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT158 (i+1))
      = (∑ i ∈ Finset.range 111, stT158 (i+1)) + stT158 112 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 111
    simpa using h
  have hprev := st158_p111
  have hstep := st158_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p113 : ((2988352585669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT158 (i+1))
      = (∑ i ∈ Finset.range 112, stT158 (i+1)) + stT158 113 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 112
    simpa using h
  have hprev := st158_p112
  have hstep := st158_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p114 : ((6336695664863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT158 (i+1))
      = (∑ i ∈ Finset.range 113, stT158 (i+1)) + stT158 114 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 113
    simpa using h
  have hprev := st158_p113
  have hstep := st158_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p115 : ((5559437827283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT158 (i+1))
      = (∑ i ∈ Finset.range 114, stT158 (i+1)) + stT158 115 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 114
    simpa using h
  have hprev := st158_p114
  have hstep := st158_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p116 : ((4900971223653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT158 (i+1))
      = (∑ i ∈ Finset.range 115, stT158 (i+1)) + stT158 116 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 115
    simpa using h
  have hprev := st158_p115
  have hstep := st158_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p117 : ((5398228340653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT158 (i+1))
      = (∑ i ∈ Finset.range 116, stT158 (i+1)) + stT158 117 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 116
    simpa using h
  have hprev := st158_p116
  have hstep := st158_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p118 : ((6265486376869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT158 (i+1))
      = (∑ i ∈ Finset.range 117, stT158 (i+1)) + stT158 118 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 117
    simpa using h
  have hprev := st158_p117
  have hstep := st158_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p119 : ((308495979471/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT158 (i+1))
      = (∑ i ∈ Finset.range 118, stT158 (i+1)) + stT158 119 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 118
    simpa using h
  have hprev := st158_p118
  have hstep := st158_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p120 : ((5266479459721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT158 (i+1))
      = (∑ i ∈ Finset.range 119, stT158 (i+1)) + stT158 120 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 119
    simpa using h
  have hprev := st158_p119
  have hstep := st158_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p121 : ((981847521163/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT158 (i+1))
      = (∑ i ∈ Finset.range 120, stT158 (i+1)) + stT158 121 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 120
    simpa using h
  have hprev := st158_p120
  have hstep := st158_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p122 : ((2808238119431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT158 (i+1))
      = (∑ i ∈ Finset.range 121, stT158 (i+1)) + stT158 122 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 121
    simpa using h
  have hprev := st158_p121
  have hstep := st158_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p123 : ((6352565448709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT158 (i+1))
      = (∑ i ∈ Finset.range 122, stT158 (i+1)) + stT158 123 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 122
    simpa using h
  have hprev := st158_p122
  have hstep := st158_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p124 : ((303323286043/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT158 (i+1))
      = (∑ i ∈ Finset.range 123, stT158 (i+1)) + stT158 124 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 123
    simpa using h
  have hprev := st158_p123
  have hstep := st158_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p125 : ((323263705609/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT158 (i+1))
      = (∑ i ∈ Finset.range 124, stT158 (i+1)) + stT158 125 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 124
    simpa using h
  have hprev := st158_p124
  have hstep := st158_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p126 : ((491798786899/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT158 (i+1))
      = (∑ i ∈ Finset.range 125, stT158 (i+1)) + stT158 126 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 125
    simpa using h
  have hprev := st158_p125
  have hstep := st158_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p127 : ((2822343145239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT158 (i+1))
      = (∑ i ∈ Finset.range 126, stT158 (i+1)) + stT158 127 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 126
    simpa using h
  have hprev := st158_p126
  have hstep := st158_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p128 : ((6359836909661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT158 (i+1))
      = (∑ i ∈ Finset.range 127, stT158 (i+1)) + stT158 128 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 127
    simpa using h
  have hprev := st158_p127
  have hstep := st158_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p129 : ((3055328915399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT158 (i+1))
      = (∑ i ∈ Finset.range 128, stT158 (i+1)) + stT158 129 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 128
    simpa using h
  have hprev := st158_p128
  have hstep := st158_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p130 : ((5235341547031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT158 (i+1))
      = (∑ i ∈ Finset.range 129, stT158 (i+1)) + stT158 130 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 129
    simpa using h
  have hprev := st158_p129
  have hstep := st158_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p131 : ((2437964944853/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT158 (i+1))
      = (∑ i ∈ Finset.range 130, stT158 (i+1)) + stT158 131 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 130
    simpa using h
  have hprev := st158_p130
  have hstep := st158_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p132 : ((548654449839/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT158 (i+1))
      = (∑ i ∈ Finset.range 131, stT158 (i+1)) + stT158 132 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 131
    simpa using h
  have hprev := st158_p131
  have hstep := st158_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p133 : ((1571349970141/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT158 (i+1))
      = (∑ i ∈ Finset.range 132, stT158 (i+1)) + stT158 133 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 132
    simpa using h
  have hprev := st158_p132
  have hstep := st158_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p134 : ((196092959671/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT158 (i+1))
      = (∑ i ∈ Finset.range 133, stT158 (i+1)) + stT158 134 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 133
    simpa using h
  have hprev := st158_p133
  have hstep := st158_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p135 : ((5476965393883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT158 (i+1))
      = (∑ i ∈ Finset.range 134, stT158 (i+1)) + stT158 135 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 134
    simpa using h
  have hprev := st158_p134
  have hstep := st158_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p136 : ((194741043631/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT158 (i+1))
      = (∑ i ∈ Finset.range 135, stT158 (i+1)) + stT158 136 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 135
    simpa using h
  have hprev := st158_p135
  have hstep := st158_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p137 : ((2588209206039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT158 (i+1))
      = (∑ i ∈ Finset.range 136, stT158 (i+1)) + stT158 137 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 136
    simpa using h
  have hprev := st158_p136
  have hstep := st158_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p138 : ((602643753711/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT158 (i+1))
      = (∑ i ∈ Finset.range 137, stT158 (i+1)) + stT158 138 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 137
    simpa using h
  have hprev := st158_p137
  have hstep := st158_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p139 : ((3210152330677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT158 (i+1))
      = (∑ i ∈ Finset.range 138, stT158 (i+1)) + stT158 139 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 138
    simpa using h
  have hprev := st158_p138
  have hstep := st158_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p140 : ((5909020537709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT158 (i+1))
      = (∑ i ∈ Finset.range 139, stT158 (i+1)) + stT158 140 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 139
    simpa using h
  have hprev := st158_p139
  have hstep := st158_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p141 : ((5084188235741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT158 (i+1))
      = (∑ i ∈ Finset.range 140, stT158 (i+1)) + stT158 141 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 140
    simpa using h
  have hprev := st158_p140
  have hstep := st158_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p142 : ((4875899906613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT158 (i+1))
      = (∑ i ∈ Finset.range 141, stT158 (i+1)) + stT158 142 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 141
    simpa using h
  have hprev := st158_p141
  have hstep := st158_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p143 : ((1101701890687/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT158 (i+1))
      = (∑ i ∈ Finset.range 142, stT158 (i+1)) + stT158 143 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 142
    simpa using h
  have hprev := st158_p142
  have hstep := st158_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p144 : ((3139889155797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT158 (i+1))
      = (∑ i ∈ Finset.range 143, stT158 (i+1)) + stT158 144 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 143
    simpa using h
  have hprev := st158_p143
  have hstep := st158_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p145 : ((3176819445177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT158 (i+1))
      = (∑ i ∈ Finset.range 144, stT158 (i+1)) + stT158 145 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 144
    simpa using h
  have hprev := st158_p144
  have hstep := st158_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p146 : ((1414655291199/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT158 (i+1))
      = (∑ i ∈ Finset.range 145, stT158 (i+1)) + stT158 146 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 145
    simpa using h
  have hprev := st158_p145
  have hstep := st158_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p147 : ((987310132683/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT158 (i+1))
      = (∑ i ∈ Finset.range 146, stT158 (i+1)) + stT158 147 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 146
    simpa using h
  have hprev := st158_p146
  have hstep := st158_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p148 : ((4940538978303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT158 (i+1))
      = (∑ i ∈ Finset.range 147, stT158 (i+1)) + stT158 148 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 147
    simpa using h
  have hprev := st158_p147
  have hstep := st158_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p149 : ((565869079983/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT158 (i+1))
      = (∑ i ∈ Finset.range 148, stT158 (i+1)) + stT158 149 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 148
    simpa using h
  have hprev := st158_p148
  have hstep := st158_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p150 : ((3176308026651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT158 (i+1))
      = (∑ i ∈ Finset.range 149, stT158 (i+1)) + stT158 150 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 149
    simpa using h
  have hprev := st158_p149
  have hstep := st158_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p151 : ((1581229889619/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT158 (i+1))
      = (∑ i ∈ Finset.range 150, stT158 (i+1)) + stT158 151 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 150
    simpa using h
  have hprev := st158_p150
  have hstep := st158_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p152 : ((350669005427/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT158 (i+1))
      = (∑ i ∈ Finset.range 151, stT158 (i+1)) + stT158 152 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 151
    simpa using h
  have hprev := st158_p151
  have hstep := st158_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p153 : ((983630343473/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT158 (i+1))
      = (∑ i ∈ Finset.range 152, stT158 (i+1)) + stT158 153 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 152
    simpa using h
  have hprev := st158_p152
  have hstep := st158_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p154 : ((983735100333/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT158 (i+1))
      = (∑ i ∈ Finset.range 153, stT158 (i+1)) + stT158 154 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 153
    simpa using h
  have hprev := st158_p153
  have hstep := st158_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p155 : ((1401117778209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT158 (i+1))
      = (∑ i ∈ Finset.range 154, stT158 (i+1)) + stT158 155 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 154
    simpa using h
  have hprev := st158_p154
  have hstep := st158_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p156 : ((1579687119489/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT158 (i+1))
      = (∑ i ∈ Finset.range 155, stT158 (i+1)) + stT158 156 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 155
    simpa using h
  have hprev := st158_p155
  have hstep := st158_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p157 : ((3196239826533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT158 (i+1))
      = (∑ i ∈ Finset.range 156, stT158 (i+1)) + stT158 157 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 156
    simpa using h
  have hprev := st158_p156
  have hstep := st158_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p158 : ((2882023852179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT158 (i+1))
      = (∑ i ∈ Finset.range 157, stT158 (i+1)) + stT158 158 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 157
    simpa using h
  have hprev := st158_p157
  have hstep := st158_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p159 : ((2507738202467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT158 (i+1))
      = (∑ i ∈ Finset.range 158, stT158 (i+1)) + stT158 159 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 158
    simpa using h
  have hprev := st158_p158
  have hstep := st158_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p160 : ((1206200694871/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT158 (i+1))
      = (∑ i ∈ Finset.range 159, stT158 (i+1)) + stT158 160 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 159
    simpa using h
  have hprev := st158_p159
  have hstep := st158_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p161 : ((669586292173/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT158 (i+1))
      = (∑ i ∈ Finset.range 160, stT158 (i+1)) + stT158 161 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 160
    simpa using h
  have hprev := st158_p160
  have hstep := st158_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p162 : ((47919432451/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT158 (i+1))
      = (∑ i ∈ Finset.range 161, stT158 (i+1)) + stT158 162 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 161
    simpa using h
  have hprev := st158_p161
  have hstep := st158_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p163 : ((1618594901537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT158 (i+1))
      = (∑ i ∈ Finset.range 162, stT158 (i+1)) + stT158 163 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 162
    simpa using h
  have hprev := st158_p162
  have hstep := st158_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p164 : ((3044425262603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT158 (i+1))
      = (∑ i ∈ Finset.range 163, stT158 (i+1)) + stT158 164 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 163
    simpa using h
  have hprev := st158_p163
  have hstep := st158_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p165 : ((8302735081/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT158 (i+1))
      = (∑ i ∈ Finset.range 164, stT158 (i+1)) + stT158 165 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 164
    simpa using h
  have hprev := st158_p164
  have hstep := st158_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p166 : ((2403858537581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT158 (i+1))
      = (∑ i ∈ Finset.range 165, stT158 (i+1)) + stT158 166 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 165
    simpa using h
  have hprev := st158_p165
  have hstep := st158_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p167 : ((4990745560237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT158 (i+1))
      = (∑ i ∈ Finset.range 166, stT158 (i+1)) + stT158 167 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 166
    simpa using h
  have hprev := st158_p166
  have hstep := st158_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p168 : ((5704674834481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT158 (i+1))
      = (∑ i ∈ Finset.range 167, stT158 (i+1)) + stT158 168 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 167
    simpa using h
  have hprev := st158_p167
  have hstep := st158_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p169 : ((6360818793721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT158 (i+1))
      = (∑ i ∈ Finset.range 168, stT158 (i+1)) + stT158 169 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 168
    simpa using h
  have hprev := st158_p168
  have hstep := st158_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p170 : ((6429429092269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT158 (i+1))
      = (∑ i ∈ Finset.range 169, stT158 (i+1)) + stT158 170 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 169
    simpa using h
  have hprev := st158_p169
  have hstep := st158_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p171 : ((5861450900829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT158 (i+1))
      = (∑ i ∈ Finset.range 170, stT158 (i+1)) + stT158 171 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 170
    simpa using h
  have hprev := st158_p170
  have hstep := st158_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p172 : ((2556145045467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT158 (i+1))
      = (∑ i ∈ Finset.range 171, stT158 (i+1)) + stT158 172 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 171
    simpa using h
  have hprev := st158_p171
  have hstep := st158_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p173 : ((2384876938819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT158 (i+1))
      = (∑ i ∈ Finset.range 172, stT158 (i+1)) + stT158 173 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 172
    simpa using h
  have hprev := st158_p172
  have hstep := st158_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p174 : ((2547459393997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT158 (i+1))
      = (∑ i ∈ Finset.range 173, stT158 (i+1)) + stT158 174 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 173
    simpa using h
  have hprev := st158_p173
  have hstep := st158_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p175 : ((2916129637201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT158 (i+1))
      = (∑ i ∈ Finset.range 174, stT158 (i+1)) + stT158 175 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 174
    simpa using h
  have hprev := st158_p174
  have hstep := st158_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p176 : ((802393382039/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT158 (i+1))
      = (∑ i ∈ Finset.range 175, stT158 (i+1)) + stT158 176 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 175
    simpa using h
  have hprev := st158_p175
  have hstep := st158_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p177 : ((6417085288591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT158 (i+1))
      = (∑ i ∈ Finset.range 176, stT158 (i+1)) + stT158 177 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 176
    simpa using h
  have hprev := st158_p176
  have hstep := st158_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p178 : ((5833273314727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT158 (i+1))
      = (∑ i ∈ Finset.range 177, stT158 (i+1)) + stT158 178 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 177
    simpa using h
  have hprev := st158_p177
  have hstep := st158_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p179 : ((5101786851531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT158 (i+1))
      = (∑ i ∈ Finset.range 178, stT158 (i+1)) + stT158 179 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 178
    simpa using h
  have hprev := st158_p178
  have hstep := st158_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p180 : ((4755328239543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT158 (i+1))
      = (∑ i ∈ Finset.range 179, stT158 (i+1)) + stT158 180 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 179
    simpa using h
  have hprev := st158_p179
  have hstep := st158_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p181 : ((1007847809133/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT158 (i+1))
      = (∑ i ∈ Finset.range 180, stT158 (i+1)) + stT158 181 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 180
    simpa using h
  have hprev := st158_p180
  have hstep := st158_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p182 : ((44886721497/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT158 (i+1))
      = (∑ i ∈ Finset.range 181, stT158 (i+1)) + stT158 182 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 181
    simpa using h
  have hprev := st158_p181
  have hstep := st158_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p183 : ((127455385761/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT158 (i+1))
      = (∑ i ∈ Finset.range 182, stT158 (i+1)) + stT158 183 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 182
    simpa using h
  have hprev := st158_p182
  have hstep := st158_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p184 : ((1621144707061/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT158 (i+1))
      = (∑ i ∈ Finset.range 183, stT158 (i+1)) + stT158 184 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 183
    simpa using h
  have hprev := st158_p183
  have hstep := st158_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p185 : ((6008617547189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT158 (i+1))
      = (∑ i ∈ Finset.range 184, stT158 (i+1)) + stT158 185 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 184
    simpa using h
  have hprev := st158_p184
  have hstep := st158_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p186 : ((5275427007821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT158 (i+1))
      = (∑ i ∈ Finset.range 185, stT158 (i+1)) + stT158 186 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 185
    simpa using h
  have hprev := st158_p185
  have hstep := st158_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p187 : ((478307040347/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT158 (i+1))
      = (∑ i ∈ Finset.range 186, stT158 (i+1)) + stT158 187 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 186
    simpa using h
  have hprev := st158_p186
  have hstep := st158_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p188 : ((19435228217/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT158 (i+1))
      = (∑ i ∈ Finset.range 187, stT158 (i+1)) + stT158 188 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 187
    simpa using h
  have hprev := st158_p187
  have hstep := st158_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p189 : ((2723581218901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT158 (i+1))
      = (∑ i ∈ Finset.range 188, stT158 (i+1)) + stT158 189 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 188
    simpa using h
  have hprev := st158_p188
  have hstep := st158_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p190 : ((615737297181/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT158 (i+1))
      = (∑ i ∈ Finset.range 189, stT158 (i+1)) + stT158 190 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 189
    simpa using h
  have hprev := st158_p189
  have hstep := st158_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p191 : ((40793432787/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT158 (i+1))
      = (∑ i ∈ Finset.range 190, stT158 (i+1)) + stT158 191 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 190
    simpa using h
  have hprev := st158_p190
  have hstep := st158_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p192 : ((395080433113/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT158 (i+1))
      = (∑ i ∈ Finset.range 191, stT158 (i+1)) + stT158 192 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 191
    simpa using h
  have hprev := st158_p191
  have hstep := st158_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p193 : ((2217424517/3906250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT158 (i+1))
      = (∑ i ∈ Finset.range 192, stT158 (i+1)) + stT158 193 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 192
    simpa using h
  have hprev := st158_p192
  have hstep := st158_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p194 : ((5003492200619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT158 (i+1))
      = (∑ i ∈ Finset.range 193, stT158 (i+1)) + stT158 194 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 193
    simpa using h
  have hprev := st158_p193
  have hstep := st158_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p195 : ((2361304849027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT158 (i+1))
      = (∑ i ∈ Finset.range 194, stT158 (i+1)) + stT158 195 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 194
    simpa using h
  have hprev := st158_p194
  have hstep := st158_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p196 : ((625517069923/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT158 (i+1))
      = (∑ i ∈ Finset.range 195, stT158 (i+1)) + stT158 196 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 195
    simpa using h
  have hprev := st158_p195
  have hstep := st158_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p197 : ((2835256656367/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT158 (i+1))
      = (∑ i ∈ Finset.range 196, stT158 (i+1)) + stT158 197 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 196
    simpa using h
  have hprev := st158_p196
  have hstep := st158_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p198 : ((6313919623891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT158 (i+1))
      = (∑ i ∈ Finset.range 197, stT158 (i+1)) + stT158 198 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 197
    simpa using h
  have hprev := st158_p197
  have hstep := st158_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p199 : ((6547850353891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT158 (i+1))
      = (∑ i ∈ Finset.range 198, stT158 (i+1)) + stT158 199 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 198
    simpa using h
  have hprev := st158_p198
  have hstep := st158_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p200 : ((3118337948861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT158 (i+1))
      = (∑ i ∈ Finset.range 199, stT158 (i+1)) + stT158 200 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 199
    simpa using h
  have hprev := st158_p199
  have hstep := st158_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p201 : ((2784350975093/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT158 (i+1))
      = (∑ i ∈ Finset.range 200, stT158 (i+1)) + stT158 201 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 200
    simpa using h
  have hprev := st158_p200
  have hstep := st158_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p202 : ((2468631073337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT158 (i+1))
      = (∑ i ∈ Finset.range 201, stT158 (i+1)) + stT158 202 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 201
    simpa using h
  have hprev := st158_p201
  have hstep := st158_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p203 : ((1176855065653/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT158 (i+1))
      = (∑ i ∈ Finset.range 202, stT158 (i+1)) + stT158 203 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 202
    simpa using h
  have hprev := st158_p202
  have hstep := st158_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p204 : ((1251849511543/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT158 (i+1))
      = (∑ i ∈ Finset.range 203, stT158 (i+1)) + stT158 204 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 203
    simpa using h
  have hprev := st158_p203
  have hstep := st158_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p205 : ((353885050357/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT158 (i+1))
      = (∑ i ∈ Finset.range 204, stT158 (i+1)) + stT158 205 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 204
    simpa using h
  have hprev := st158_p204
  have hstep := st158_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p206 : ((3150066368979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT158 (i+1))
      = (∑ i ∈ Finset.range 205, stT158 (i+1)) + stT158 206 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 205
    simpa using h
  have hprev := st158_p205
  have hstep := st158_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p207 : ((3282862934907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT158 (i+1))
      = (∑ i ∈ Finset.range 206, stT158 (i+1)) + stT158 207 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 206
    simpa using h
  have hprev := st158_p206
  have hstep := st158_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p208 : ((3157703019899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT158 (i+1))
      = (∑ i ∈ Finset.range 207, stT158 (i+1)) + stT158 208 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 207
    simpa using h
  have hprev := st158_p207
  have hstep := st158_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p209 : ((1422658458517/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT158 (i+1))
      = (∑ i ∈ Finset.range 208, stT158 (i+1)) + stT158 209 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 208
    simpa using h
  have hprev := st158_p208
  have hstep := st158_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p210 : ((2516764418279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT158 (i+1))
      = (∑ i ∈ Finset.range 209, stT158 (i+1)) + stT158 210 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 209
    simpa using h
  have hprev := st158_p209
  have hstep := st158_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p211 : ((187903652737/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT158 (i+1))
      = (∑ i ∈ Finset.range 210, stT158 (i+1)) + stT158 211 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 210
    simpa using h
  have hprev := st158_p210
  have hstep := st158_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p212 : ((971805512507/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT158 (i+1))
      = (∑ i ∈ Finset.range 211, stT158 (i+1)) + stT158 212 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 211
    simpa using h
  have hprev := st158_p211
  have hstep := st158_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p213 : ((1085673480287/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT158 (i+1))
      = (∑ i ∈ Finset.range 212, stT158 (i+1)) + stT158 213 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 212
    simpa using h
  have hprev := st158_p212
  have hstep := st158_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p214 : ((610422994169/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT158 (i+1))
      = (∑ i ∈ Finset.range 213, stT158 (i+1)) + stT158 214 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 213
    simpa using h
  have hprev := st158_p213
  have hstep := st158_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p215 : ((3267595067109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT158 (i+1))
      = (∑ i ∈ Finset.range 214, stT158 (i+1)) + stT158 215 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 214
    simpa using h
  have hprev := st158_p214
  have hstep := st158_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p216 : ((650176003357/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT158 (i+1))
      = (∑ i ∈ Finset.range 215, stT158 (i+1)) + stT158 216 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 215
    simpa using h
  have hprev := st158_p215
  have hstep := st158_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p217 : ((9413821289/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT158 (i+1))
      = (∑ i ∈ Finset.range 216, stT158 (i+1)) + stT158 217 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 216
    simpa using h
  have hprev := st158_p216
  have hstep := st158_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p218 : ((2674488592279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT158 (i+1))
      = (∑ i ∈ Finset.range 217, stT158 (i+1)) + stT158 218 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 217
    simpa using h
  have hprev := st158_p217
  have hstep := st158_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p219 : ((300883877819/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT158 (i+1))
      = (∑ i ∈ Finset.range 218, stT158 (i+1)) + stT158 219 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 218
    simpa using h
  have hprev := st158_p218
  have hstep := st158_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p220 : ((146392904397/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT158 (i+1))
      = (∑ i ∈ Finset.range 219, stT158 (i+1)) + stT158 220 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 219
    simpa using h
  have hprev := st158_p219
  have hstep := st158_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p221 : ((78447802803/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT158 (i+1))
      = (∑ i ∈ Finset.range 220, stT158 (i+1)) + stT158 221 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 220
    simpa using h
  have hprev := st158_p220
  have hstep := st158_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p222 : ((282731767523/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT158 (i+1))
      = (∑ i ∈ Finset.range 221, stT158 (i+1)) + stT158 222 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 221
    simpa using h
  have hprev := st158_p221
  have hstep := st158_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p223 : ((1255501203913/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT158 (i+1))
      = (∑ i ∈ Finset.range 222, stT158 (i+1)) + stT158 223 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 222
    simpa using h
  have hprev := st158_p222
  have hstep := st158_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p224 : ((3295372415977/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT158 (i+1))
      = (∑ i ∈ Finset.range 223, stT158 (i+1)) + stT158 224 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 223
    simpa using h
  have hprev := st158_p223
  have hstep := st158_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p225 : ((6447964093897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT158 (i+1))
      = (∑ i ∈ Finset.range 224, stT158 (i+1)) + stT158 225 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 224
    simpa using h
  have hprev := st158_p224
  have hstep := st158_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p226 : ((5920137696161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT158 (i+1))
      = (∑ i ∈ Finset.range 225, stT158 (i+1)) + stT158 226 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 225
    simpa using h
  have hprev := st158_p225
  have hstep := st158_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p227 : ((5257000428177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT158 (i+1))
      = (∑ i ∈ Finset.range 226, stT158 (i+1)) + stT158 227 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 226
    simpa using h
  have hprev := st158_p226
  have hstep := st158_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p228 : ((4766895032963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT158 (i+1))
      = (∑ i ∈ Finset.range 227, stT158 (i+1)) + stT158 228 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 227
    simpa using h
  have hprev := st158_p227
  have hstep := st158_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p229 : ((1168402629707/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT158 (i+1))
      = (∑ i ∈ Finset.range 228, stT158 (i+1)) + stT158 229 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 228
    simpa using h
  have hprev := st158_p228
  have hstep := st158_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p230 : ((1254115765597/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT158 (i+1))
      = (∑ i ∈ Finset.range 229, stT158 (i+1)) + stT158 230 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 229
    simpa using h
  have hprev := st158_p229
  have hstep := st158_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p231 : ((1409263243201/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT158 (i+1))
      = (∑ i ∈ Finset.range 230, stT158 (i+1)) + stT158 231 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 230
    simpa using h
  have hprev := st158_p230
  have hstep := st158_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p232 : ((1563770171017/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT158 (i+1))
      = (∑ i ∈ Finset.range 231, stT158 (i+1)) + stT158 232 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 231
    simpa using h
  have hprev := st158_p231
  have hstep := st158_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p233 : ((6595900177987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT158 (i+1))
      = (∑ i ∈ Finset.range 232, stT158 (i+1)) + stT158 233 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 232
    simpa using h
  have hprev := st158_p232
  have hstep := st158_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p234 : ((6511461651301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT158 (i+1))
      = (∑ i ∈ Finset.range 233, stT158 (i+1)) + stT158 234 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 233
    simpa using h
  have hprev := st158_p233
  have hstep := st158_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p235 : ((6042001344529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT158 (i+1))
      = (∑ i ∈ Finset.range 234, stT158 (i+1)) + stT158 235 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 234
    simpa using h
  have hprev := st158_p234
  have hstep := st158_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p236 : ((674257556963/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT158 (i+1))
      = (∑ i ∈ Finset.range 235, stT158 (i+1)) + stT158 236 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 235
    simpa using h
  have hprev := st158_p235
  have hstep := st158_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p237 : ((2423830504617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT158 (i+1))
      = (∑ i ∈ Finset.range 236, stT158 (i+1)) + stT158 237 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 236
    simpa using h
  have hprev := st158_p236
  have hstep := st158_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p238 : ((2317536716289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT158 (i+1))
      = (∑ i ∈ Finset.range 237, stT158 (i+1)) + stT158 238 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 237
    simpa using h
  have hprev := st158_p237
  have hstep := st158_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p239 : ((2421828990561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT158 (i+1))
      = (∑ i ∈ Finset.range 238, stT158 (i+1)) + stT158 239 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 238
    simpa using h
  have hprev := st158_p238
  have hstep := st158_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p240 : ((1345650697833/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT158 (i+1))
      = (∑ i ∈ Finset.range 239, stT158 (i+1)) + stT158 240 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 239
    simpa using h
  have hprev := st158_p239
  have hstep := st158_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p241 : ((1506237822399/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT158 (i+1))
      = (∑ i ∈ Finset.range 240, stT158 (i+1)) + stT158 241 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 240
    simpa using h
  have hprev := st158_p240
  have hstep := st158_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p242 : ((325228628059/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT158 (i+1))
      = (∑ i ∈ Finset.range 241, stT158 (i+1)) + stT158 242 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 241
    simpa using h
  have hprev := st158_p241
  have hstep := st158_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p243 : ((331307995259/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT158 (i+1))
      = (∑ i ∈ Finset.range 242, stT158 (i+1)) + stT158 243 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 242
    simpa using h
  have hprev := st158_p242
  have hstep := st158_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p244 : ((1268598015011/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT158 (i+1))
      = (∑ i ∈ Finset.range 243, stT158 (i+1)) + stT158 244 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 243
    simpa using h
  have hprev := st158_p243
  have hstep := st158_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p245 : ((1154466472223/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT158 (i+1))
      = (∑ i ∈ Finset.range 244, stT158 (i+1)) + stT158 245 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 244
    simpa using h
  have hprev := st158_p244
  have hstep := st158_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p246 : ((5144700287161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT158 (i+1))
      = (∑ i ∈ Finset.range 245, stT158 (i+1)) + stT158 246 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 245
    simpa using h
  have hprev := st158_p245
  have hstep := st158_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p247 : ((1177426170799/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT158 (i+1))
      = (∑ i ∈ Finset.range 246, stT158 (i+1)) + stT158 247 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 246
    simpa using h
  have hprev := st158_p246
  have hstep := st158_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p248 : ((927450086819/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT158 (i+1))
      = (∑ i ∈ Finset.range 247, stT158 (i+1)) + stT158 248 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 247
    simpa using h
  have hprev := st158_p247
  have hstep := st158_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p249 : ((4952932440007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT158 (i+1))
      = (∑ i ∈ Finset.range 248, stT158 (i+1)) + stT158 249 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 248
    simpa using h
  have hprev := st158_p248
  have hstep := st158_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_p250 : ((1382853274463/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT158 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT158 (i+1))
      = (∑ i ∈ Finset.range 249, stT158 (i+1)) + stT158 250 := by
    have h := Finset.sum_range_succ (fun i => stT158 (i+1)) 249
    simpa using h
  have hprev := st158_p249
  have hstep := st158_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st158_s250 :
    |Real.sin (((158 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))
      - ((-404113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -1040021/10000000) (δ := 8099/1000000000) (ψ := -555919/1000000) 158 139
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 158`** (evaluated boundary). -/
theorem station_158_sign : 0 < hardyG ((((158:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 158 250 (by norm_num) (by norm_num)
    ((-555919/1000000 : ℚ) : ℝ)
  have hchain := st158_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT158 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((158 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-555919/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st158_c250
  have hsinb := abs_le.mp st158_s250
  have hbdy_lo : ((16035156426159/399428000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((158 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ))) / 2
          - ((((158:ℕ)):ℝ))
            * Real.sin (((158 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-555919/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((158:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((158:ℝ) * Real.log (250:ℝ) - ((-555919/1000000 : ℚ) : ℝ))) / 2
        - ((158:ℝ)) * Real.sin ((158:ℝ) * Real.log (250:ℝ) - ((-555919/1000000 : ℚ) : ℝ))
        ≥ ((126769149/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((158:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((126769149/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((126769149/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((126769149/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((158:ℕ)):ℝ))+1) * (((((158:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((4462214251/7812500000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1382853274463/2500000000000 : ℚ) : ℝ) + ((16035156426159/399428000000000 : ℚ) : ℝ)
      - ((4462214251/7812500000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-555919/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((158:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-555919/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((158:ℕ)):ℝ)))).re
      - Real.sin ((-555919/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((158:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((158:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((158:ℕ)):ℝ))
      = (((((158:ℕ)):ℝ)) * (Real.log ((((158:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((158:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_158
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
  have hθwin : |(((-555919/1000000 : ℚ) : ℝ) + ((28:ℤ)) * (2*Real.pi)) - theta ((((158:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((158:ℕ)):ℝ)))
    (φ := ((-555919/1000000 : ℚ) : ℝ) + ((28:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-555919/1000000 : ℚ)) : ℝ) 28).1,
    (cos_sin_shift (((-555919/1000000 : ℚ)) : ℝ) 28).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_158_sign
end AxiomAudit
